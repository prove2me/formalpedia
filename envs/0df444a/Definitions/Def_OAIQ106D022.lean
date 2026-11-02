-- Prove2me | Definitions.Def_OAIQ106D022
-- name    : OAIQ106D022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:09:30.240221+00:00
-- url     : https://prove2.me/theorems/8eeda6bf-3286-4778-9306-0812cc037c67
-- title:
--   Definitions bundle OAIQ106D022 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7486 declarations of OpenAI's Lean: 7486 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw25030step3`, `OAI.MUB6.Certificate.MixedSemantics.raw25031`, `OAI.MUB6.Certificate.MixedSemantics.raw25031Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25031step0`, `OAI.MUB6.Certificate.MixedSemantics.raw25031step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25031step1`, `OAI.MUB6.Certificate.MixedSemantics.raw25031step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25031step2`, `OAI.MUB6.Certificate.MixedSemantics.raw25031step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25032`, `OAI.MUB6.Certificate.MixedSemantics.raw25032Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25032step0`, `OAI.MUB6.Certificate.MixedSemantics.raw25032step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25032step1`, `OAI.MUB6.Certificate.MixedSemantics.raw25032step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25032step2`, `OAI.MUB6.Certificate.MixedSemantics.raw25032step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25032step3`, `OAI.MUB6.Certificate.MixedSemantics.raw25032step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25033`, `OAI.MUB6.Certificate.MixedSemantics.raw25033Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25033step0`, `OAI.MUB6.Certificate.MixedSemantics.raw25033step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25033step1`, `OAI.MUB6.Certificate.MixedSemantics.raw25033step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25033step2`, `OAI.MUB6.Certificate.MixedSemantics.raw25033step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25033step3`, `OAI.MUB6.Certificate.MixedSemantics.raw25033step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25034`, `OAI.MUB6.Certificate.MixedSemantics.raw25034Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25034step0`, `OAI.MUB6.Certificate.MixedSemantics.raw25034step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25034step1`, `OAI.MUB6.Certificate.MixedSemantics.raw25034step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25034step2`, `OAI.MUB6.Certificate.MixedSemantics.raw25034step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25034step3`, `OAI.MUB6.Certificate.MixedSemantics.raw25034step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25035` and 7446 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical1`, `MutuallyUnbiased_MixedSemantics_Canonical19`, `MutuallyUnbiased_MixedSemantics_Canonical195`, `MutuallyUnbiased_MixedSemantics_Canonical196`, `MutuallyUnbiased_MixedSemantics_Canonical197`, `MutuallyUnbiased_MixedSemantics_Canonical198`, `MutuallyUnbiased_MixedSemantics_Canonical199`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical20`, `MutuallyUnbiased_MixedSemantics_Canonical200`, `MutuallyUnbiased_MixedSemantics_Canonical201`, `MutuallyUnbiased_MixedSemantics_Canonical202`, `MutuallyUnbiased_MixedSemantics_Canonical203`, `MutuallyUnbiased_MixedSemantics_Canonical204`, `MutuallyUnbiased_MixedSemantics_Canonical205`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1164`, `OAI.MUB6.Certificate.MixedSemantics.sound1165`, `OAI.MUB6.Certificate.MixedSemantics.sound2636`, `OAI.MUB6.Certificate.MixedSemantics.sound2637`, `OAI.MUB6.Certificate.MixedSemantics.sound2638`, `OAI.MUB6.Certificate.MixedSemantics.sound2640`, `OAI.MUB6.Certificate.MixedSemantics.sound5418`, `OAI.MUB6.Certificate.MixedSemantics.sound5433`, `OAI.MUB6.Certificate.MixedSemantics.sound5434`, `OAI.MUB6.Certificate.MixedSemantics.sound5435`, `OAI.MUB6.Certificate.MixedSemantics.sound5439`, `OAI.MUB6.Certificate.MixedSemantics.sound5443`, `OAI.MUB6.Certificate.MixedSemantics.sound5450`, `OAI.MUB6.Certificate.MixedSemantics.sound5451`, `OAI.MUB6.Certificate.MixedSemantics.sound5452`, `OAI.MUB6.Certificate.MixedSemantics.sound5453`, `OAI.MUB6.Certificate.MixedSemantics.sound5464`, `OAI.MUB6.Certificate.MixedSemantics.sound5465`, `OAI.MUB6.Certificate.MixedSemantics.sound5476`, `OAI.MUB6.Certificate.MixedSemantics.sound5482`, `OAI.MUB6.Certificate.MixedSemantics.sound5483`, `OAI.MUB6.Certificate.MixedSemantics.sound5485`, `OAI.MUB6.Certificate.MixedSemantics.sound5490`, `OAI.MUB6.Certificate.MixedSemantics.sound5491`, `OAI.MUB6.Certificate.MixedSemantics.sound5492`, `OAI.MUB6.Certificate.MixedSemantics.sound5498`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound101`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound124`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound94`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound95`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero733`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero863`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1471`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1472`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1483`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1490`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1741`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound18`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound20`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound426`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound503`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound612`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound642`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound682`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound693`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound721`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound757`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound791`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound816`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound821`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound851`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound871`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound886`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound896`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound934`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound943`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound946`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound953`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound955`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound957`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound960`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound961`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound969`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound974`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound979`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound989`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1913`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw25step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw26 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw252 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw252Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw252step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw253 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw253Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw253step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw254 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw254Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw254step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw255 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw255Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw255step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2504 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2504Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw2504step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw2504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2505 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2505Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2505step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2505step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2506 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2507 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2507Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2507step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2508 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw2508step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw2508step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2509 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2510 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2510Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw2510step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2510step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2510step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2511 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2511step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2511step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2512 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2513 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2513Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2513step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2514 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2514step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2514step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2515 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2516 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2516Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw2516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2516step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2517 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw2517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2517step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2517step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2518 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw2518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2519 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw2519Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2519step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2520 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2520step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2520step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2521 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2522 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2522Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw2522step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2522step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2522step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2523 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2523step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2524 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2525 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2525Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2525step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2526 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2526step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2527 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2528 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2528Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2528step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2528step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2528step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2529 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2529step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2529step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2530 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2531 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2531Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw2531step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2531step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2532 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2532step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2532step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2533 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2534 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2534Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw2534step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw2534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2535 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2535step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2535step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2536 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2537 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2537Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2537step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2537step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2537step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2538 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2538step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2538step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2539 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2540 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2540Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2540step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw2540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw2540step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2541 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2541step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2541step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2542 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2543 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2543Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw2543step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2543step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2544 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0]]
def raw2544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2544step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2544step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2545 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0]]
def raw2545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2545step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2546 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0]]
def raw2546Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2546step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw2546step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw2546step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw2546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2547 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2547step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2548 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2549 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2549Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0]]
def raw2549step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw2549step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2549step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw2549step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2550 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2550step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2551 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2552 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2552Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2552step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2552step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2552step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2553 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2553step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2553step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2553step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2554 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2554step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2555 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2555Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2555step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2555step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2556 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2556step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2556step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2557 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2558 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2558Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw2558step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2558step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2558step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2559 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2559step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2559step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical195
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25030step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw25031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25031Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25031step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25031step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25031step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25032Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25032step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25032step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25032step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25032step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25032step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25033Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25033step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25033step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25033step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25033step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25033step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25033step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25034Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25034step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25034step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25034step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25034step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25034step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25034step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25035Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25035step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25035step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25035step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25036Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25036step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25036step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25036step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25037Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25037step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25037step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25037step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25037step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25038Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25038step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25038step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25038step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25038step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25039Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25039step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25039step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25039step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25039step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25040Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25040step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25040step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25040step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25040step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25040step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25041Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25041step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25041step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25041step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25041step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25041step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25042Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25042step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25042step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25042step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25042step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25043Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25043step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw25043step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25043step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25043step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25043step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25044Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25044step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25044step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25044step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25044step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25044step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25045Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25045step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25045step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25045step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25045step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25045step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25046Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25046step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25046step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25046step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25046step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25046step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25047Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25047step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25047step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25047step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25047step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25048Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25048step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw25048step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25048step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25048step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25048step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25049Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25049step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25049step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25049step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25049step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25049step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25050Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25050step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25050step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25050step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25050step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25050step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25051Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25051step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25051step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25051step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25051step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25051step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25052Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25052step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25052step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25053Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25053step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25053step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25053step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25053step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25053step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25054Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25054step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25054step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25054step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25054step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25054step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25061 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1], ![0, 0]]
def raw25061Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25061step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw25061step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25061step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw25061step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25067step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25067step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25067step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25068step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25069step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25069step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25069step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25070step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25070step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25071step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25072step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25072step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25072step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25073step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25073step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25073step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25074step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25074step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25075step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25076step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25076step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25076step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25081Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25084step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25084step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25087 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25087step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical196
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25089 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw25089step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25089step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25089step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25089step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25092 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25092step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25092step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25094 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25094step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25094step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25095 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25095step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25095step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25097 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25097step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25099 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25099step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25099step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25100step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25100step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25100step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25101 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25101step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25101step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25101step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25102 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25102step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25102step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25103 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25103step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25103step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25104 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25104step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25104step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25107 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25107step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25107step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25107step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25108 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25108step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25109 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25110 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25110step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25111 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25111step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25112 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25112step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25114 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25115 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25116 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25116step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25117 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25118 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25119 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25120 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25120step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25121 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25122 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25122step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25123 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25123Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25123step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25123step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25123step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25124 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25124Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25125 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25125Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25125step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25125step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25126 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25126Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25126step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25127 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25127Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25127step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25128 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25128Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25128step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25128step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25128step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25129 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25129Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25130 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25130Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25130step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25130step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25131 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25131Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25131step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25131step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25132 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25132Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25132step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25133 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25133Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25133step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25133step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25134 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25134Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25134step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25138step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25138step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25142step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25143step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25143step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25144step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25150step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25153step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25153step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25160step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25161step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw25164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25164step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25168step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25168step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25168step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw25168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25171step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25173step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25175step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25177step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25183step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25183step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25183step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25184step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25186Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25186step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25187Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25187step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25188Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25188step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw25188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25189Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25189step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25189step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25190Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25190step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25191Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25191step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25192Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25193Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25193step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw25193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw25194Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25194step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25194step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25194step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25194step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw25194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25195step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25195step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25195step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25195step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25196step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25197step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw25197step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25197step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25197step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25197step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25198step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25198step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25198step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25198step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25198step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25198step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25198step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25198step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25198step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25199step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25199step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25199step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25199step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25200step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25200step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25200step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25200step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25201step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25201step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25201step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25201step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25202step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25202step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25203step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25203step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25203step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25203step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25203step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25203step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25203step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25203step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25203step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25204step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25204step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25204step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25205step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25205step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25205step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25205step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25205step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25206step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25206step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25206step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25206step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw25207step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25207step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25207step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25207step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25208step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25208step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25208step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25209step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25209step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25209step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25209step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25210step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw25210step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25210step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25210step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25210step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25211step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw25211step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw25211step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25211step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw25211step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw25212step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25212step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25212step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25213Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25213step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25213step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw25213step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25213step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25213step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25213step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25214step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25214step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25214step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25214step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25214step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25215Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25215step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25215step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25215step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25215step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25215step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical197
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25216Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25216step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25216step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25216step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25216step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25216step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25217Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25217step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25217step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25217step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25217step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25218Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25218step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw25218step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25218step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25218step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25218step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25219Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25219step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25219step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25219step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25219step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25219step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25220step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw25220step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25220step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25220step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25220step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25221Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25221step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw25221step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25221step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw25221step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25221step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw25221step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw25222step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25222step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25222step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25222step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25223Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25223step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw25223step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25223step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25223step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25223step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw25224Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25224step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25224step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25224step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw25224step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25224step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25224step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25224step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25224step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25225step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25228step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25231 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![0, 0], ![1, -1]]
def raw25231Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25231step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw25231step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25231step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw25231step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25232Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25232step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25233step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25233step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25234Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25234step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25234step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25235Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25235step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25235step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25236Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25236step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25236step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25237Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25237step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25238Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25238step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25239Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25239step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25240Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25240step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25241step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25241step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25242step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25242step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25242step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25243step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25243step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25244step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25244step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25245step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25245step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25246step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25246step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25247step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25248step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25249step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25250step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25251step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25252step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25253step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25253step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25254step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25255step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25262step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25263step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25264step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25271step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25272 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25272step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25272step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25273 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw25273step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25273step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25273step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25273step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25274 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25274step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25275 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25275step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25275step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25276 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25276step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25276step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25277 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25277step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25278 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25278step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25279 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25279step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25280 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25280step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25280step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25281 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw25281step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25281step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25281step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25281step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25281step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25282 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25282step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25282step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25282step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25283 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25283step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25283step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25284 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25284step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25284step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25284step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25285 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25285step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25286 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25286step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25286step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25286step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25286step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25286step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25287 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25287step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25287step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25288 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25288step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25289 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25289step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25289step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25290 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25290Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25290step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25290step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25291 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25291Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25291step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25292 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25292Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25292step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25292step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25293 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25293Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25293step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25293step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25294 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25294step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25295 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25295step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25296 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25296step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25297 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25297step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25298 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25298step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25299 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25299step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25300 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25300step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25301 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25302 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25303 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25303step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25304 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25304step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25304step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25305 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25306 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25307 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25308 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25308step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25309 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25309Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25309step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25309step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25310 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25310step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25310step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25311 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25311step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25311step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25312 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25312step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25313 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25313step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25314 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25314step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25314step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25315 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25315Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25315step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25315step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25315step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25316 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25316step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25317 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25317step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25317step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25317step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25318 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25319 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25319step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25320 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25320step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25321 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25321Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25321step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25321step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25321step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25321step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25321step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25321step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25322 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25322step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25322step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25322step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25322step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25322step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25323 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25323Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25323step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25324 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25324step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25325 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25325Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25325step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25325step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25326 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25326step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25326step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25327 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25327Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25327step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25327step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25327step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25327step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25327step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25327step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25328 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25328step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25329 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25329Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25329step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25329step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25330 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25330step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25330step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25331 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25331Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25331step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw25331step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25331step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25331step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25331step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25332 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25332step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25333 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25333Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25333step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25333step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw25338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw25338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw25339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw25339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25340 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![-1, 1], ![2, -2]]
def raw25340Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25340step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![-1, 1], ![2, -2]]
def raw25340step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25340step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw25340step1Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical198
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25346 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25346step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25346step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25347 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw25347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25347step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25347step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25348 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25349 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw25349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25350 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25351 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw25351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25351step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25351step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25352step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25354step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25360step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25361step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25361step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25363step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25364step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25364step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25366step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25367step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25368step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25368step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25371step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25371step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw25371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25375step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25381step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25384step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25384step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25385step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25388step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25389Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25389step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25389step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw25390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw25390step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25390step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25390step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25391Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25391step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw25391step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25391step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25391step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25391step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25392Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw25392step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25392step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25392step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25392step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25393Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25393step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25393step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25393step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw25393step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25393step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25393step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25393step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25393step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25394Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25394step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw25394step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25394step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25394step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25394step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25395Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25395step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25395step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25395step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25395step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25395step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25396Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25396step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25396step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25396step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25397Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25397step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25397step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25397step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25397step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25397step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25397step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25397step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25398Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25398step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25398step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25398step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25398step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25398step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25398step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25399Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw25399step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25399step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25399step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25400Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw25400step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25400step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25400step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25401Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25401step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw25401step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25401step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25401step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25401step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25402Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw25402step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25402step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25402step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25402step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25403Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25403step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25403step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25403step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25403step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25403step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25403step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25404step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw25404step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25404step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25404step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25404step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25405Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25405step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25405step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25405step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25405step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25405step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25406step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25406step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25406step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25406step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25406step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25406step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25406step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25407Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25407step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw25407step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25407step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25407step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25407step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25408step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25408step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25408step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25408step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25408step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25409Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25409step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw25409step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25409step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25409step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25409step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25410step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25410step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25410step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25411Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25411step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw25411step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25411step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25411step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25411step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25411step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw25412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw25412step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25412step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25412step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25412step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw25412step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25412step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw25412step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25412step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw25412step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25427step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25427step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25428step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25428step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25429step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25430step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25430step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25431step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25431step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25432step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25433step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25434step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25434step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25435step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25435step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25436step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25436step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25437step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25437step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25438step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25438step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25439step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25439step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25440step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25440step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25440step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25441step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25441step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25442step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25442step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25443step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25443step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25444step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25444step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25444step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25445step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25445step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25445step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25446step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25446step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25446step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25447step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25447step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25448step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw25448step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw25448step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25449Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25449step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25450Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25450step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25451Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25452Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25452step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25453Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25453step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25454Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25455Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25456Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25457Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25458Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25458step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25459Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25459step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25460Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25461Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25461step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25461step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25462Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25462step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25463Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25463step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25464Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25464step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25464step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25465Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25466Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25466step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25466step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25467Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25467step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25467step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25468Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25468step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25468step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25469Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25470Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25470step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw25470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25471 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw25471step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25471step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25471step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25471step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25471step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical199
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25472 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25472step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25473 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25473step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25474 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25474step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25474step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25474step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25475 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw25475step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25475step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25475step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25475step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25476 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25476step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25477 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25477step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25478 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25478step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25478step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25478step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25478step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25478step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25479 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25479step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25480 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25480step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25480step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25480step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25481 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw25481step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25481step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25481step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25481step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25481step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25482 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25482step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25483 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25483step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25483step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25483step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25484 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25484step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25484step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25485 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25485Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25485step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25485step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25485step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25485step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25485step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25485step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25486 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25486Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25486step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25486step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25486step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25487 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25487Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25487step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25487step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25488 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25488Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25488step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25488step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25489 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25489Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25489step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25489step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25489step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25490 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25490Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw25490step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25490step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25490step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25491 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25491Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25491step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25492 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25492Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25492step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25492step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25493 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25493Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25493step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25493step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25493step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25494 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25494Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25494step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw25494step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25494step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25494step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25494step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25494step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25495 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25495Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25495step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25496 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25496step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25497 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25497Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25497step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw25497step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25497step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25497step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25497step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25498 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25498step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25499 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25499step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25499step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25499step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25500 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25500step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25500step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw25501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw25501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw25502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw25503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw25503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw25503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw25504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw25504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw25504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25505Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25508Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25511 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![2, -2], ![1, -1], ![0, 0]]
def raw25511Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25511step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![2, -2], ![1, -1]]
def raw25511step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25511step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw25511step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25517step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25522 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![2, -2], ![0, 0], ![1, -1]]
def raw25522Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25522step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![2, -2], ![1, -1]]
def raw25522step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25522step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw25522step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25529 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw25529Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25529step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw25529step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw25540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25543 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25546 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25546step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25548 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25550step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw25553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25553step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25555 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]
def raw25555Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25555step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw25555step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25555step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw25555step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25563step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25564 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw25564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25564step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25565 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw25565step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25565step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25565step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25566 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw25566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25569step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw25570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw25571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25573 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]
def raw25573Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25573step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![0, 0], ![3, -3]]
def raw25573step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25573step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw25573step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25573step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw25573step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25585Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25585step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25586Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25586step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25587step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25588Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![0, -1, 1], ![2, -1, -1]]
def raw25589Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![0, -1, 1], ![2, -1, -1]]
def raw25589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![0, -1, 1], ![2, -1, -1]]
def raw25589step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1], ![1, 0, -1]]
def raw25590Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1], ![1, 0, -1]]
def raw25590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, -2, 1], ![1, 0, -1]]
def raw25590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw25590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25591 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![3, -3], ![-1, 1], ![1, -1]]
def raw25591Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25591step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3], ![-1, 1], ![1, -1]]
def raw25591step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25591step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![3, -3], ![-1, 1], ![1, -1]]
def raw25591step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25591step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw25591step2Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw256 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw256Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw256step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw257 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw257Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw257step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw258 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 3, -2]]
def raw258Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw258step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw258step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw259 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 3, -2]]
def raw259Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw259step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw259step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw259step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw260 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 3, -3]]
def raw260Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw260step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw260step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw261 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 3, -3]]
def raw261Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw261step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw261step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw261step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw262 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2560 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2560step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2561 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2561Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2561step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw2561step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2561step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2562 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2563 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2564 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2564Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2564step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2565 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2566 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2567 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2567Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2567step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2567step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2567step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2568 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2569 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2570 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2570Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2570step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 2, 0]]
def raw2570step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2570step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2570step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2570step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2570step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2571 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2571step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2572 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2573 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2573Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2573step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2573step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2573step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2573step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2573step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2574 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2574step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2574step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2575 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2576 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2576Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2576step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2576step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2577 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2577step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw2577step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw2577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2578 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2578step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw2578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2579 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2579Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2579step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]
def raw2579step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]
def raw2579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2580 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2580step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2580step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2581 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2581Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2582 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2582Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2582step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2583 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2583step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2583step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2584 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2584Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2585Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2585step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2585step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2585step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2585step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2585step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2586 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2586step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2586step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2587 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2588 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2588Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw2588step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2588step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2588step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2588step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2588step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2589 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2589step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2590 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2590Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2591 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2591Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw2591step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2591step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2591step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2592 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 1, -2], ![-1, 2, -1]]
def raw2592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2592step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2592step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2593 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 1, -2], ![-1, 2, -1]]
def raw2593Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2593step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2594 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 1, -2], ![-1, 2, -1]]
def raw2594Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2594step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2594step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2595 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2595step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2595step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2596 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2596Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2597 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2597Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2597step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2598 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2598step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2599 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2599Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2600 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2600Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2600step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2601 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2601step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2602 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2602Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2602step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2603 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2603Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2603step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2603step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2603step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2604 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2604step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2605 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2605Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2605step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2606 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2606Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2606step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2607 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2607step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2608 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2608Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2608step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2609 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2609Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2609step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2610 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2610step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2611 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2611Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2612 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2612Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2612step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2613 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2614 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2615 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2615Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2615step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2615step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2616 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2617 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2617Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2618 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2618Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2618step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2619 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2620 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2620Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2621 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2621Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2621step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2621step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2621step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2622 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2623 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2623Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2624 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2624Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2624step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2624step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical200
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25606step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25607step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25607step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25607step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25607step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25607step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25612step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25613step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25615step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25616step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25618step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25618step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25619step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25620step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25621step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25622step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25622step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25623step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25623step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25623step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25624step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25626step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25626step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25626step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25627step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25627step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25628step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw25628step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25629step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw25629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw25630step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw25632step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25633step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25633step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25633step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25633step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25633step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25634step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25634step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25634step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25634step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25634step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25635step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25635step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw25635step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25635step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25635step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25635step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25635step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25636step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25636step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw25636step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25636step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25636step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25636step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25636step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25637Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25637step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25637step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25637step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25637step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25637step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25637step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25637step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25638Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25638step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25638step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25638step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25638step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25638step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25639Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25639step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25639step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25639step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25640step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw25640step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25640step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25640step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25640step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25641Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25641step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw25641step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25641step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25641step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25641step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25641step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25642Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25642step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25642step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25642step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25642step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25642step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25643Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25643step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25643step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25643step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25643step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25643step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25644Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25644step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25644step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25644step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25645Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25645step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw25645step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25645step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25645step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25645step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25646Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25646step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw25646step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25646step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25646step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25646step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25646step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25647Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25647step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25647step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25647step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25647step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25647step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25648Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25648step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25648step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw25648step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25648step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25648step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25648step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25648step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25649Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25649step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw25649step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25649step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25649step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25649step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25650Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25650step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw25650step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25650step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25650step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25650step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25650step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25651Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25651step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25651step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25651step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25651step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25651step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25651step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25651step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25651step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25652Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25652step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25652step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25652step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25652step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25652step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25652step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25652step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25652step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25653Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25653step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25653step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25653step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25653step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25653step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25653step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25653step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25653step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25654Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25654step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25654step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25654step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25654step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25654step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25655Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25655step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25655step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25655step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25655step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25655step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25656Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25656step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25656step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw25656step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25656step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25656step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25656step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25656step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25657Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25657step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25657step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25657step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25657step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25657step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25657step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25657step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25658Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25658step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25658step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw25658step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25658step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25658step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25658step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25658step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25659Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25659step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw25659step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25659step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25659step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25659step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25659step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25660Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25660step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw25660step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25660step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25660step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25660step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25661Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25661step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25661step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw25661step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25661step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw25661step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25661step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw25661step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25662Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25662step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25662step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw25662step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25662step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw25662step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25662step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw25662step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25697 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25697step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25697step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25698 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25698step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25698step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25699 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25699step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25699step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25699step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25700 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25700step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25700step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25701 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25701step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25702 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25702step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25702step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25703 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25703step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25703step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25704 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw25704step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25704step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw25704step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25704step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw25704step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25705 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25705step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25705step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25706 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25706step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25706step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25707 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw25707step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25707step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw25707step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25708 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw25708step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25708step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw25708step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25709 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw25709step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25709step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25709step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25709step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25709step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25710 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25710step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25710step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25711 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25711step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25711step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25712 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25712step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25712step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25712step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25712step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25713step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25713step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25713step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25713step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25713step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25713step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25714 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25714step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25714step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical201
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25733Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25733step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25733step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25734step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25734step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25735step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25735step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25735step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw25735step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25735step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25735step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25735step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25735step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25736step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25736step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw25736step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25737step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25737step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25737step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25737step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25737step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25737step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25737step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25738step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25738step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25740step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25740step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25741step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25741step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25742step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25742step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25743step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25743step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25745step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25746step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25746step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25747step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25748step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25748step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25750step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw25751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw25751step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25751step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![2, -1, -1]]
def raw25751step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25751step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw25751step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25752step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25753step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25756step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25757step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25758step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25759step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25760step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25760step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw25762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25762step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw25762step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25763Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25763step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25763step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25763step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25763step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25763step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25764Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25764step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25764step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25764step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25764step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25764step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25765Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25765step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25765step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw25765step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25765step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25765step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25765step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25765step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25766Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25766step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25766step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25766step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw25766step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25766step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw25766step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25766step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw25766step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25766step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw25766step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25767Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25767step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25767step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25767step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25767step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25767step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25767step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25767step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25767step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25767step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25768Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25768step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25768step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25768step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25768step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25768step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25769Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25769step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25769step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25769step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25769step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25770Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25770step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw25770step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25770step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25770step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25770step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25771Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25771step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25771step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25771step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25771step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25771step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25771step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25771step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25771step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25772Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25772step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25772step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25772step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25772step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25773Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25773step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25773step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25773step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25773step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25773step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25774Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25774step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25774step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25774step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25775Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25775step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw25775step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25775step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25775step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25775step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25776Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25776step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25776step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25776step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25776step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25776step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25776step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25776step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25776step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25777Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25777step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25777step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25777step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25777step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25777step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25778Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25778step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25778step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25778step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25778step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw25778step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25778step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25778step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25778step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25778step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25779Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25779step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw25779step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25779step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25779step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25779step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25780Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25780step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw25780step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25780step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25780step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25780step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25781Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw25781step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw25781step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25781step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![2, -1, -1]]
def raw25781step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25781step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw25781step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25781step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw25781step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25781step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw25781step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25782Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25782step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25782step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25782step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25782step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25782step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25782step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25782step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25782step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25783Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25783step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25783step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25783step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25783step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25783step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25783step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25783step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25783step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25784Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25784step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25784step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25784step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25784step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25784step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25785Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25785step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25785step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25785step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25785step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25785step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25786Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25786step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25786step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw25786step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25786step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25786step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25786step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25786step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25787Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25787step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25787step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25787step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25787step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25787step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25787step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25787step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25788Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25788step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25788step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25788step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw25788step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25788step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25788step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25788step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25788step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25789Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25789step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw25789step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25789step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25789step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25789step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25790step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw25790step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25790step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25790step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25790step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25791Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25791step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25791step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25791step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw25791step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25791step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25791step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25791step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25791step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw25792Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25792step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25792step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25792step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw25792step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25792step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]
def raw25792step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25792step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw25792step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25792step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw25792step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25793step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25793step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25794step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25795step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25795step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25796step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25796step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25797step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25797step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25797step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25798step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25799step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25799step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25800step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25800step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25801step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25801step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25801step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25801step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25802step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25802step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25802step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25803step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25803step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25804step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25804step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25804step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw25804step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25804step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw25804step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25805step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25805step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25805step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25805step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25805step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25805step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25806step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25806step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25806step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25806step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25806step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25807step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25807step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25807step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25808step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25808step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw25809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw25809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw25809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25809step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25809step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25809step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25810step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25810step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25810step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25811step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25811step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25812step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25812step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw25813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw25813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw25813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25813step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw25813step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25813step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw25813step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25836 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25836step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25836step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25837 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25837step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25837step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25837step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25837step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25837step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25838 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25838step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw25838step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25838step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25838step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25838step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25838step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25839 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25839step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25839step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25839step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25840 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25840step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25840step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25840step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25841 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25841step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25841step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw25841step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25841step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw25841step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25841step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw25841step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25842 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw25842step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw25842step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw25843step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25843step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw25843step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25844 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25844step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25844step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25844step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25844step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25844step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25845 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25845step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25845step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25845step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw25845step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25845step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25845step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25845step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25845step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25846 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25846step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25846step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25846step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25847 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25847step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25847step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25847step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25847step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25848step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, 0, -2]]
def raw25852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, 0, -2]]
def raw25852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25852step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, -1, 1], ![2, 0, -2]]
def raw25852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25852step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 1, -2]]
def raw25853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 1, -2]]
def raw25853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -2, 1], ![1, 1, -2]]
def raw25853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw25853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25854 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![-1, 1], ![2, -2]]
def raw25854Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25854step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![-1, 1], ![2, -2]]
def raw25854step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25854step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![2, -2]]
def raw25854step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25854step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw25854step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25855step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical202
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25858step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25858step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25858step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25859step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw25859step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw25859step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw25859step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25868step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25870step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25870step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25871step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25873step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25873step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25874step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25874step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25874step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25875step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25875step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25878step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25878step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw25879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw25879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw25879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25879step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25880step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25883step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25884step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25884step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw25888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25888step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![2, 0, -2]]
def raw25888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25888step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw25888step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw25888step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw25888step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25889step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25889step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25889step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25889step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25889step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw25893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25893step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25897step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw25898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25898step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25900step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw25903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25903step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw25903step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25904step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25904step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw25909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw25909step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw25909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25909step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25909step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25910step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25910step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25910step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25910step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25911step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25911step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25912step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25912step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25913step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw25914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25914step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25914step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw25914step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25915step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw25915step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw25916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw25917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 1, -3]]
def raw25919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 1, -3]]
def raw25919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25919step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, -1, 1], ![2, 1, -3]]
def raw25919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25919step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw25919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 2, -3]]
def raw25920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 2, -3]]
def raw25920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, -2, 1], ![1, 2, -3]]
def raw25920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw25920step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25921 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![-1, 1], ![3, -3]]
def raw25921Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25921step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![-1, 1], ![3, -3]]
def raw25921step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25921step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw25921step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25921step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw25921step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25922step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25924step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25924step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw25924step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25924step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw25924step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25924step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw25924step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25924step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw25924step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25925step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25925step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw25925step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25925step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25925step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25925step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25925step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25928step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25932step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25934step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25934step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25935step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25937step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25937step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw25937step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25938step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw25938step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw25942step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25943Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25943step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25943step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25944Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25944step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25945Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25945step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25945step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25945step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw25945step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25945step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw25945step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25946Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25946step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25946step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25946step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw25946step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25946step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw25946step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25947step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25947step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25948step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25950step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25951step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25951step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25952step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25953step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25955step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25955step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25955step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25956step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25956step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25956step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25958step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25958step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25961step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25961step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw25961step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25961step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw25961step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25962step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw25962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25963step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25966step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25966step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw25966step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25966step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw25966step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25967step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25967step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw25967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25968step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25968step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25968step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25969step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25971step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25971step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw25971step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25971step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![3, -3, 0]]
def raw25971step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw25972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25972step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25972step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw25972step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25972step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![3, -3, 0]]
def raw25972step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25973Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25973step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25973step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25973step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25973step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25973step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25974Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25974step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25974step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25974step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25974step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25975Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25975step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25975step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25975step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw25975step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25975step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw25975step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25975step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw25975step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25975step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw25975step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25976Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25976step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25976step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw25976step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25976step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25976step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25976step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25977step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25977step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25977step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25977step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25977step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25978Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25978step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25978step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25979Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25979step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25979step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25979step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25979step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25979step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25979step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25979step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25980step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw25980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25980step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25980step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25980step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25981step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25981step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25981step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25981step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25981step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25982step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25982step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25983Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25983step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25983step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25983step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25983step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25983step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25983step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25983step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical203
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25984Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25984step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw25984step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25984step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25984step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25984step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25985step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25985step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25985step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25985step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25985step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25985step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25985step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25985step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25986step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25986step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25986step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25986step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25987step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25987step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25987step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25987step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25988step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25988step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25988step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw25988step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25988step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw25988step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25988step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw25988step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25988step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw25988step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25989step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25989step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw25989step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25989step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw25989step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25989step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw25989step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25990step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25990step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25990step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25990step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25990step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25991step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25991step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25992step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25992step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25992step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25992step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25993step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25993step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw25993step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw25993step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25993step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw25993step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25998step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25998step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw26000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw26001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw26001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26057 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26057Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26057step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw26057step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw26057step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26057step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw26057step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26058Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26058step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26059 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26059Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26059step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw26059step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26059step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw26059step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26060Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26060step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw26060step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw26060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26061 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26061Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26061step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26061step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26061step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26061step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![-1, 1, 0], ![-3, 2, 1]]
def raw26061step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26061step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw26061step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26061step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw26061step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26062 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26062Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26062step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26062step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26062step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26063Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26063step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26063step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26064Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26064step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26064step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw26064step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26064step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw26064step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26065 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26065Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26065step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26065step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26065step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26065step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![-1, 1, 0], ![-3, 2, 1]]
def raw26065step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26065step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw26065step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26065step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw26065step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26066 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26066Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26066step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26066step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26066step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26067 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26067Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26067step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26067step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26067step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26067step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26068Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26068step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26068step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw26068step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26068step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw26068step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26069 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26069Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26069step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26069step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw26069step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26069step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw26069step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26070 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26070step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26071 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26071Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26071step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26071step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26071step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26071step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26072step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26072step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26072step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw26072step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26072step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw26072step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -4, 2]]
def raw26073Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -4, 2]]
def raw26073step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-2, 1, 1], ![2, -4, 2]]
def raw26073step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw26073step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26073step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw26073step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw26074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw26075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 2, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw26076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![0, 1, -1], ![2, -2, 0]]
def raw26078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![0, 1, -1], ![2, -2, 0]]
def raw26078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw26078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw26079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw26079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26080 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![3, -3], ![1, -1], ![0, 0]]
def raw26080Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26080step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![3, -3], ![1, -1]]
def raw26080step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26080step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![3, -3], ![1, -1]]
def raw26080step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26080step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw26080step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26085Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26085step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw26085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw26086step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 2, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26087step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw26087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26088step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![0, 0, 0], ![2, -1, -1]]
def raw26089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw26089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw26089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, 0, -1]]
def raw26090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, 0, -1]]
def raw26090step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26091 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![3, -3], ![0, 0], ![1, -1]]
def raw26091Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26091step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![3, -3], ![1, -1]]
def raw26091step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26091step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![3, -3], ![1, -1]]
def raw26091step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26091step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw26091step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 2, -2], ![2, -2, 0]]
def raw26096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![0, 2, -2], ![2, -2, 0]]
def raw26096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26098 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2], ![0, 0]]
def raw26098Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26098step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw26098step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26098step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw26098step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2], ![1, -1, 0]]
def raw26102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2], ![1, -1, 0]]
def raw26102step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26103Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26103step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26106Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26106step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw26107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw26107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26109 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw26109Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26109step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw26109step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26109step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw26109step1Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical204
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw26114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw26117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw26117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2]]
def raw26128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw26128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw26128step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]
def raw26129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]
def raw26129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26129step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26130 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![0, 0], ![2, -2]]
def raw26130Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26130step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw26130step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26130step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw26130step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26131step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 0, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw26132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw26133Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw26133step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![3, -1, -2]]
def raw26134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![3, -1, -2]]
def raw26134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw26134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26136step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw26136step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw26136step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw26136step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw26137step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26137step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26137step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26137step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26137step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw26138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw26138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw26138step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26138step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26138step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26138step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26139step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26139step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26139step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26139step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw26161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26165 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw26165step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26165step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26165step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26165step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26165step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26167 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26167step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26167step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26167step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26167step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw26167step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw26167step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw26167step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw26167step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw26167step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26180Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26180step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26181Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26181step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26182Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 1, -3]]
def raw26183Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw26183step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw26183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]
def raw26184Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]
def raw26184step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26185 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![1, -1], ![0, 0], ![3, -3]]
def raw26185Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26185step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![1, -1], ![3, -3]]
def raw26185step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26185step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw26185step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw26195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26196step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26205 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26205step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw26206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw26207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw26208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw26209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw26210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw26211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw26212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw26213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26214step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26214step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26214step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26214step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26215step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26215step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26215step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26215step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26215step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26216step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26216step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26216step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26216step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26217step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26217step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26217step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26217step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26218step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26218step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26218step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26218step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26218step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26223step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26223step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw26223step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26223step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical205
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw26240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw26243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw26243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26244Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26244step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26244step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26244step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26244step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26244step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26244step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26245Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26245step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26245step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26245step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26245step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26245step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26246Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26246step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26246step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26246step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26246step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26246step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26247Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26247step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26247step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26247step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26247step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26247step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26248Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26248step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26248step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26248step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26248step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26248step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26249Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26249step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26249step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26249step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26249step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26249step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26250Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26250step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26250step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26250step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26251Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26251step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26251step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26251step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26251step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26251step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26252Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26252step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26252step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26252step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26252step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26252step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26253Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26253step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26253step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26253step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26254Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26254step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26254step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26254step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26255Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26255step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26255step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26255step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26255step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26256Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26256step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26256step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26256step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26257Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26257step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26257step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26257step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26257step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26258Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26258step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26258step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26258step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26259Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26259step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw26259step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26259step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26259step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26259step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26259step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26260Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26260step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw26260step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26280Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


