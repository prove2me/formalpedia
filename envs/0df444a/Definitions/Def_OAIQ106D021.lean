-- Prove2me | Definitions.Def_OAIQ106D021
-- name    : OAIQ106D021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:08:29.594292+00:00
-- url     : https://prove2.me/theorems/5fc3b60b-40d5-4a23-bd9c-fb073d9eddd0
-- title:
--   Definitions bundle OAIQ106D021 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7449 declarations of OpenAI's Lean: 7449 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw23884step1`, `OAI.MUB6.Certificate.MixedSemantics.raw23884step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23885`, `OAI.MUB6.Certificate.MixedSemantics.raw23885step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23885step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23885step1`, `OAI.MUB6.Certificate.MixedSemantics.raw23885step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23886`, `OAI.MUB6.Certificate.MixedSemantics.raw23886Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23886step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23886step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23886step1`, `OAI.MUB6.Certificate.MixedSemantics.raw23886step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23887`, `OAI.MUB6.Certificate.MixedSemantics.raw23887Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23887step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23887step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23888`, `OAI.MUB6.Certificate.MixedSemantics.raw23888Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23888step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23888step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23888step1`, `OAI.MUB6.Certificate.MixedSemantics.raw23888step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23889`, `OAI.MUB6.Certificate.MixedSemantics.raw23889Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23889step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23889step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23889step1`, `OAI.MUB6.Certificate.MixedSemantics.raw23889step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2388Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2388step0`, `OAI.MUB6.Certificate.MixedSemantics.raw2388step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2388step1`, `OAI.MUB6.Certificate.MixedSemantics.raw2388step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2389`, `OAI.MUB6.Certificate.MixedSemantics.raw23890`, `OAI.MUB6.Certificate.MixedSemantics.raw23890Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23890step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23890step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23890step1` and 7409 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical1`, `MutuallyUnbiased_MixedSemantics_Canonical18`, `MutuallyUnbiased_MixedSemantics_Canonical186`, `MutuallyUnbiased_MixedSemantics_Canonical187`, `MutuallyUnbiased_MixedSemantics_Canonical188`, `MutuallyUnbiased_MixedSemantics_Canonical189`, `MutuallyUnbiased_MixedSemantics_Canonical19`, `MutuallyUnbiased_MixedSemantics_Canonical190`, `MutuallyUnbiased_MixedSemantics_Canonical191`, `MutuallyUnbiased_MixedSemantics_Canonical192`, `MutuallyUnbiased_MixedSemantics_Canonical193`, `MutuallyUnbiased_MixedSemantics_Canonical194`, `MutuallyUnbiased_MixedSemantics_Canonical195`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1163`, `OAI.MUB6.Certificate.MixedSemantics.sound1164`, `OAI.MUB6.Certificate.MixedSemantics.sound2598`, `OAI.MUB6.Certificate.MixedSemantics.sound2599`, `OAI.MUB6.Certificate.MixedSemantics.sound2601`, `OAI.MUB6.Certificate.MixedSemantics.sound5176`, `OAI.MUB6.Certificate.MixedSemantics.sound5177`, `OAI.MUB6.Certificate.MixedSemantics.sound5386`, `OAI.MUB6.Certificate.MixedSemantics.sound5387`, `OAI.MUB6.Certificate.MixedSemantics.sound5388`, `OAI.MUB6.Certificate.MixedSemantics.sound5415`, `OAI.MUB6.Certificate.MixedSemantics.sound5416`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound102`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound114`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound84`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound86`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound87`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound89`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound90`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound95`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound98`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1423`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1780`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero863`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound14`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1422`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1428`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1430`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1436`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1438`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1465`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1674`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1785`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1942`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1950`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2063`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound446`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound757`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound791`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound814`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound821`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound843`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound851`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound871`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound886`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound896`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound901`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound934`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound943`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound946`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound953`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound955`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound960`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound969`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound974`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound989`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1882`.
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

def raw23Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw23step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw24 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw24Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]

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

def raw238Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw238step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw238step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw238step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw239 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 3, -1]]
def raw239Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw239step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw239step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw240 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw240Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw240step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw241 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw241Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw241step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw242 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 3, -2]]
def raw242Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw242step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw242step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw242step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw243 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 3, -2]]
def raw243Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw243step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw243step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw243step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw244 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 1, 1], ![0, 3, -3]]
def raw244Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw244step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw244step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw244step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw245 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 1, 1], ![0, 3, -3]]
def raw245Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw245step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw245step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw245step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw246 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 2, -2], ![-2, 2, 0]]
def raw246Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw246step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw246step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw247 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 2, -2], ![-2, 2, 0]]
def raw247Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw247step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw247step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw248 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw248Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw248step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw248step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw249 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw249Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw249step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw249step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2388step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2388step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2389 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2389Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2389step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2390 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2390Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw2390step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2390step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2390step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2390step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2391 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2391step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2391step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2392 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2392step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2393 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2393Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw2393step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2393step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2393step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2393step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2394 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2394step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2395 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2396 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2396Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw2396step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2396step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2396step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2397 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2397step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2397step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2397step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2398 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2398step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2399 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2399Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw2399step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2399step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2399step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2400 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2400step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2400step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2401 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2402 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2402Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw2402step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw2402step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw2402step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2403 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2403step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2403step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2404 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2405 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2405Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw2405step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw2405step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2405step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw2405step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2406 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2406step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2406step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2406step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2407 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2408 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2408Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2408step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2408step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2408step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2409 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw2409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2409step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2409step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2410 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw2410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2411 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw2411Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2411step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2412 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2412step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2412step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2413 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2414 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2414Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2414step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2414step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2414step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2414step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2415 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2415step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2415step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2416 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2417 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2417Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2417step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2417step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2418 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2418step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2419 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2420 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2420Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw2420step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw2420step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw2420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2421 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2421step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2421step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2422 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2423 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2423Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw2423step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw2423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2424 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2424step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2424step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2425 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2426 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2426Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2426step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2426step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2426step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2427 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2427step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2428 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2429 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2429Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw2429step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2429step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2429step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2429step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2430 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2430step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2430step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2430step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2431 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23885 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]

def raw23885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23886 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23887 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23888 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw23888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23888step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23889 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw23889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23890 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23891 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23892 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw23892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw23892step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23893 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23893step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23893step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23894 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23895 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw23895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw23895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23896 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw23896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23896step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23897 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw23897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw23897step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw23898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw23898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw23898step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw23900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw23901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw23902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw23903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw23903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw23904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw23910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw23910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23911 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]
def raw23911Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23911step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw23911step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23911step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw23911step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23911step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw23911step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23912 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23913 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23914 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw23914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23917 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23919 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23920 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23920step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw23932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw23932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23933Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23933step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23934step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23935step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw23936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw23936step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23937 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23938 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23938Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23938step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw23938step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23939 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23939Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23939step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23939step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23939step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23940 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23940Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23940step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw23940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23940step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23941 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23941Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23941step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw23941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23941step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23942 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23942Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23942step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23942step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23943 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23943step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23943step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23943step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23943step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23944 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23944Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23944step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23945 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23945Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23945step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23945step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23945step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw23945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23946 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23946step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23946step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23946step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw23946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23947 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23947step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23947step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw23947step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23948 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23948step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw23948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw23948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23949 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw23949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23950 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23950Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw23950step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23951 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23951step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23951step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23952 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23952step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23953 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23953Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw23953step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23954 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw23954Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw23954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23954step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23955Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23955step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23956Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23956step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23957Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23958Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23958step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23959Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23959step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23960Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23960step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23961step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw23961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23962Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23962step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw23963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw23964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw23964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw23965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw23965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw23965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23966 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23967 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw23967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23968 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23969 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23969step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23970 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23971 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23972 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23973 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-1, -1, 2]]
def raw23973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-1, -1, 2]]
def raw23973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw23973step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw23973step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23974 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23974Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23974step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23975 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23975step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23976 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23976step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23976step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23977 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23977Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23977step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23977step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23977step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23978 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23979 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23979step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23980 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23980Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23980step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23980step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23981 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw23981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw23981step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23982 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23983 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23983step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23984 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23985 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23985step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23987step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23987step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23988step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23989step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw23990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw23990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23990step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![1, 1, -2]]
def raw23991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2], ![1, 1, -2]]
def raw23991step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw23991step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23992 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![-2, 2], ![2, -2]]
def raw23992Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23992step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-2, 2], ![2, -2]]
def raw23992step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23992step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw23992step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw23996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw23996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw23997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw23997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw23998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23998step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw23999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw23999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23999step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw24000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw24000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24001 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw24001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24002 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24002step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw24002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24002step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24003 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw24003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24004 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw24004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24005 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw24005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw24005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24006 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw24006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw24006step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24007 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24008 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24008step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24008step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw24008step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24009 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24009step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw24009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24010 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw24010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24011 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24011step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw24015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24016step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24028 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw24028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24029 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw24029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24030 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw24030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24031 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24032 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw24032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24033 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24033step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24034 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24035 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw24035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24036 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24037 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24038 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24038Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24038step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24039Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw24044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24045 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw24045Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24045step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw24045step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24047step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24050 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw24050step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24051 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw24051step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24052 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24052step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw24058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24059 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw24059Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24059step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24059step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24063step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical188
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24066 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw24066Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24066step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw24066step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw24070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24070step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw24075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24077 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]
def raw24077Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24077step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![1, -1], ![2, -2]]
def raw24077step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24077step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw24077step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24078 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw24078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24079 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-3, 2, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24079step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw24079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24079step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![3, -2, -1]]
def raw24079step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24080 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24080step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24080step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24080step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw24080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24080step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -1, -1], ![2, -1, -1]]
def raw24080step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24081 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24081step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24081step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24081step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24081step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24082 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24082step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24082step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24082step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw24082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24082step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24082step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24083 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw24083step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24084 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw24084step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24085 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24085Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 2, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24085step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 2, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24085step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw24085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24086 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24086step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24086step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24086step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24086step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24086step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24087 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24087step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw24087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24088 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, 2, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24088step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-3, 2, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24088step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw24088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24088step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]
def raw24088step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24089 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24089step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw24089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24089step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24089step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24090 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24090step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24090step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw24090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24090step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24090step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24091 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24091step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24091step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24091step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw24091step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24091step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24091step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24092 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw24092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24093 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 2, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 2, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24093step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24093step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![2, 2, -4]]
def raw24093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24095step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, -2, 2], ![2, 0, -2]]
def raw24098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, -2, 2], ![2, 0, -2]]
def raw24098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, -2, 2], ![2, 0, -2]]
def raw24098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24098step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24098step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2], ![1, 1, -2]]
def raw24099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2], ![1, 1, -2]]
def raw24099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24099step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -3, 2], ![1, 1, -2]]
def raw24099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24099step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw24099step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24100 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![-2, 2], ![2, -2]]
def raw24100Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24100step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![-2, 2], ![2, -2]]
def raw24100step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24100step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-2, 2], ![2, -2]]
def raw24100step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24100step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw24100step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24101step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24101step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24102step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24103step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24104step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24104step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24105step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24105step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24105step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24106step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24107step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24107step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24107step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24107step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24107step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24107step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24107step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24108step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24109step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24109step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24110step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24110step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw24110step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw24111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw24111step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw24111step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24111step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw24111step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24112step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24114step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24114step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24117step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24117step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24117step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24118step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24118step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24119step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24120step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24120step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24121step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24121step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24121step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw24121step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24121step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw24121step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24122step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24122step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24123step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24123step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24123step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24124step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24125step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24125step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24125step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24126step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24126step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24126step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24127step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24128step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24128step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24128step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24128step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24129step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24130step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24130step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24131step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24131step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24131step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24131step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24132step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24132step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24132step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24132step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24132step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24133step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24133step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24134step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24134step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24135Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24135step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24135step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24136Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24136step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24137Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24137step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24137step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24138Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24138step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24139Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24139step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24139step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24140Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24141Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24141step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24141step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24142Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24142step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24142step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24143Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24143step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24143step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24143step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24143step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24143step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24144Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24144step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24144step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24145Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24145step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24145step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24146Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24146step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24146step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24146step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24146step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24147Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24147step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24147step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24147step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24147step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24148Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24148step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24148step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24148step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24148step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24149Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24149step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24149step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24150Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24150step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24150step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw24151Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw24151step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw24151step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24151step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24151step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24152 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24152step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24153 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24153step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24154 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24154step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24154step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24154step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24154step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24155 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24155step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24155step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24155step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24155step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24155step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24155step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24156 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24156step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24156step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24156step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24156step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24156step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24157 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24157step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24157step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24157step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24158 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24158step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24158step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24159 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24159step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24159step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24160 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24160step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24160step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24161 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24161step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24161step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24161step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24162 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24162step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24162step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24163 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24163step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24163step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24163step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24164 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24164step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24164step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24165 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24165step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24165step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24165step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24166 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24166step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24166step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24166step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24166step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24166step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24167 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24167step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24167step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24167step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24167step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24167step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24167step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24167step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24168 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24168step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24168step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24168step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24169 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24169step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24169step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24169step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24170 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24170step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24170step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24170step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24170step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24170step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24171 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24171step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24171step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24171step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24171step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24171step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24171step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24172 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24172step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24172step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24172step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24172step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24172step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24173 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24173step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24173step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24173step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24174 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24174step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24174step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24174step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24175 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24175step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24175step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24175step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24175step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24175step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24175step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24176 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24176step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24176step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24176step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24176step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24176step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24177 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24177Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24177step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24177step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24177step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24177step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw24177step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24177step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw24177step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24178 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24178Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24178step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw24178step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw24178step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24179 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24179step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw24179step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24179step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw24179step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24180 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24180step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24180step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24180step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24180step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24180step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24180step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24180step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24181 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24181step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24181step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24181step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24181step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24181step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24182 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24182step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24183 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24183step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24184 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24184step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24184step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24184step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24184step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24184step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24185 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24185step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24185step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24185step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24185step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24185step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24185step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24185step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24186 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24186step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24186step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24186step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24186step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24186step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24187 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24187step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24187step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24188 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24188step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24189 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24189step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24190 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24190step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24191 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24191step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24191step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24191step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical189
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24192 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24192step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24193 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24193step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24194 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24194step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24195 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24195step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24196 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24196step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24196step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24197 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24197step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24197step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24197step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24197step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24197step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24197step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24197step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24198 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24198step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24199 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24199step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24199step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24200 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24200step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24200step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24200step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24200step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24200step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24200step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24201 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24201step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24201step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24201step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24201step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24201step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24201step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24202 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24202step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24202step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24202step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24202step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24202step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24203 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24203step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24203step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24203step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24204 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24204step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24205 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24205step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24205step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24205step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24205step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24205step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24206 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24206step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24206step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24206step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24206step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24206step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24206step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24207 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24207step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24207step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24207step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24207step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24207step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24207step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24208 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24208step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24208step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24209 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24209step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24209step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24209step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24209step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24210 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24210step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24210step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24210step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24210step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24210step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24210step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24211 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24211step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24211step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24211step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24211step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24211step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24211step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24212 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw24212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24212step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24213 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24213step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24213step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24214 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24214step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24215 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24215step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24215step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24215step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24215step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24215step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24215step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24216 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24217 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24217step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24217step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24217step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24217step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24218 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24218step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24218step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24218step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24219step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24219step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24220step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24220step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24221step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24221step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24221step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24223step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24224step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24225step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24225step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24225step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24227step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24227step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24227step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24227step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24227step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24228step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24228step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24228step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24229step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24230step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24230step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24230step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24230step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24231step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24231step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24231step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24231step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24232Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24232step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24233Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24233step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24233step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24234Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24234step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24234step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw24234step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24235Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24235step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24235step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24236Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24236step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24237Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24237step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24237step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24238Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24238step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24239step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24239step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24240step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24241step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24241step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24242step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24242step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24243step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24243step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24243step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24244Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24244step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24244step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24245Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24245step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24245step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24246Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24246step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24246step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24246step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24247Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24247step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24247step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24247step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24247step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24248 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24248step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24249 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24249step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24249step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24250 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24250step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24250step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24250step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24250step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24251 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24251step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24251step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24251step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24251step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24251step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24252 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24252step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24253 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24253step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24253step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24254 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24254step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24255 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24255step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24256 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24256step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24256step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24257 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24257step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24257step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24258 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24258step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24258step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24259 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24259step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24259step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24259step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24260 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24260step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24260step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24260step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24261 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24261step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24262 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24262step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24263 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24263step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24263step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24263step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24264 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24264step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24264step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24264step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24264step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24264step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24265 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24265step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24265step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24266 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24266step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24266step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24267 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24267step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24267step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24267step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24267step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24267step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24268 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24268step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24268step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24268step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24268step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24268step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24269 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24269step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24269step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24269step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24269step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24269step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24269step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24270step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24270step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24271step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24272step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24272step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24273step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24273step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24274step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24274step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24275step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24276step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24276step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24277step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24277step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24278step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24278step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24278step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24278step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24279step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24279step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24279step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24280step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24280step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw24281step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24281step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw24281step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24282step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24282step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24282step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24283step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24283step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24283step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24284step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24284step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24284step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24285step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw24286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw24286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw24286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24286step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24286step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24287step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24287step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24288step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24289step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24289step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24290Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24290step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24290step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24291Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24291step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24291step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24292Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24292step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24293Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24293step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24293step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24294step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24295step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24295step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24296step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24298step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24298step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24298step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw24298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24299step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24300step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24300step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24300step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24300step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw24303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw24303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw24303step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24303step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24306step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24307step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24307step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24307step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24307step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24308step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw24308step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24309step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24309step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24310step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24310step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24311step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24311step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24312step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24314step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24314step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24315step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24315step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24316step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24316step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24316step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24318step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24319step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24319step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24319step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24319step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24319step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24319step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

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

def raw2432 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2432Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw2432step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw2432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2433 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2433step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2434 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2435 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2435Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2435step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2435step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2435step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2436 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2436step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2436step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2437 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2438 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2438Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2438step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2438step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2438step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2438step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2439 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2439step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2439step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2440 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2441 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2441Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw2441step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw2441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2442 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2442step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2442step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2443 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2444 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2444Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2444step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2444step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2444step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2445 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2445step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2445step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2446 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2447 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2447Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw2447step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw2447step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw2447step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2448 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2448step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2448step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2449 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2450 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2450Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2450step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2450step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2451 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 2, 0], ![0, 2, -2]]
def raw2451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2451step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2451step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2451step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2452 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 2, 0], ![0, 2, -2]]
def raw2452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2452step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2453 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 2, 0], ![0, 2, -2]]
def raw2453Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2453step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]
def raw2453step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]
def raw2453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2454 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2454step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2454step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2454step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2455 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2455step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2456 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2456Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2456step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw2456step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw2456step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw2456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2457 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2457step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2457step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2458 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2459 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2459Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw2459step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw2459step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2459step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw2459step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2460 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2460step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2460step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2461 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2462 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2462Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw2462step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw2462step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2462step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw2462step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2463 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2463step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2464 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2465 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2465Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2465step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2465step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2465step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2465step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2466 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2466step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2466step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2467 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2468 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2468Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw2468step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2468step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw2468step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2468step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw2468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2469 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2469step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2470 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2470step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2471 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2471Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2471step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2471step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2472 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2472step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2473 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2474 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2474Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw2474step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2474step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2474step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2474step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2475 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2475step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2476 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2477 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2477Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2477step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2477step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2477step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2477step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2478 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2478step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2479 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2480 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2480Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2480step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2480step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2480step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2481 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2481step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2482 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2483 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2483Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2483step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2483step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2483step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2484 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2484step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2484step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2485 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2486 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2486Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2486step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2486step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2486step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2487 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2487step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2487step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2487step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2488 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2488Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2488step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2489 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2489Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw2489step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2489step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2489step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2490 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2490step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2490step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2491 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2492 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2492Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw2492step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw2492step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2492step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw2492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2493 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw2493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2493step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2493step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2494 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw2494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2495 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw2495Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2495step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2495step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2496 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2496step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2496step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2497 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2498 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2498Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw2498step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw2498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2499 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2499Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2499step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2499step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2500 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2501 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2501Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2501step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2501step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2501step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2502 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2502Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2502step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2502step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2503 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical190
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24320step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24320step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24320step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24320step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24321step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24321step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24321step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24322step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24322step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24323step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24323step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24323step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24324step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24324step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24324step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24324step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24324step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24324step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24325step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24325step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24326step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24326step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24326step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24327step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw24327step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24327step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw24327step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24328step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24328step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24328step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24328step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24328step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24328step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24329step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24329step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24329step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24329step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24329step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24330step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24330step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24330step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24331step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24331step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24331step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24332step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24332step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw24332step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24332step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw24332step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24333step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24334step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24335step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24336step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24336step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24336step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw24336step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24337step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw24337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24338step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24338step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24338step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw24338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24339step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24341Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24341step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24342Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24342step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24343Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24343step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24344Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24344step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24345Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24346Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24346step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24347Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24347step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24348Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24348step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24349Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24349step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24349step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24349step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24350Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24350step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24351Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24351step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24352Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24352step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24352step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24352step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24353Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24353step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24353step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24353step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24353step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24353step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24354Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24354step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24354step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24355Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24355step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24356Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24356step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24357step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24357step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24357step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw24357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24358step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24358step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24358step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24359step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24359step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24359step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24359step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24360step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24360step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24361step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24362step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24362step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24362step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw24362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24363step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24363step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24364Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24364step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24364step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24364step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24364step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24364step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24364step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24365Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24365step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24365step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24365step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24365step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24365step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24366Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24366step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24366step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24366step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw24366step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24366step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24366step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24366step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24366step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24367Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24367step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24367step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24367step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24367step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24367step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24367step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24367step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24367step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24368Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24368step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24368step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24368step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24368step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw24368step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24368step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24368step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24368step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24368step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24369Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24369step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24369step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24369step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24369step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24369step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24370Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24370step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24370step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24370step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24371Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24371step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24371step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24371step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24371step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24371step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24371step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24372Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24372step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24372step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24372step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24372step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24372step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24373Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24373step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw24373step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24373step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24373step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24373step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24374Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24374step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24374step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24374step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24374step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24374step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24374step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24375Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24375step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24375step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24375step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24376Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24376step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24376step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24376step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24376step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24376step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24376step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24377Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24377step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24377step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24377step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24377step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24377step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24377step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24378Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24378step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw24378step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24378step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24378step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24378step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24378step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24379Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24379step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24379step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw24379step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24379step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw24379step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24379step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw24379step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24380Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24380step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw24380step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24380step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw24380step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24380step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw24380step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24381Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24381step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw24381step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24381step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw24381step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24381step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw24381step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24382Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24382step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24382step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24382step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24382step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw24382step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24382step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24382step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24382step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24382step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24383Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24383step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24383step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24383step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24383step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw24383step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24383step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24383step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24383step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24383step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24384Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24384step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24384step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw24384step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24384step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw24384step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24384step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw24384step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24385Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24385step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw24385step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw24385step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24386Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24386step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw24386step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw24386step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24387Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24387step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24387step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24387step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw24387step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24387step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw24387step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24388Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24388step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24388step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24388step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw24388step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24388step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw24388step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24389Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24389step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24389step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24389step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24389step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw24389step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24389step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw24389step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24389step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw24389step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24390Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24390step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw24390step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24390step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw24390step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24390step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw24390step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24391Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24391step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw24391step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw24391step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24391step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw24391step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24392Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24392step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24392step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24392step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw24392step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24392step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw24392step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24392step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw24392step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24393Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24393step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24393step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24393step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw24393step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24393step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24393step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24393step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24393step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24394step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24394step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24398step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24399step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24399step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24400 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![-1, 1], ![2, -2]]
def raw24400Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24400step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![2, -2]]
def raw24400step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24400step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw24400step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24400step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw24400step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24413 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24413step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24413step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24413step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24413step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24413step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24413step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24413step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical191
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24451step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -2, 2], ![2, 1, -3]]
def raw24455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -2, 2], ![2, 1, -3]]
def raw24455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -2, 2], ![2, 1, -3]]
def raw24455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24455step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24455step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![1, 2, -3]]
def raw24456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![1, 2, -3]]
def raw24456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -3, 2], ![1, 2, -3]]
def raw24456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24457 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![-2, 2], ![3, -3]]
def raw24457Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24457step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-2, 2], ![3, -3]]
def raw24457step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24457step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![3, -3]]
def raw24457step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24457step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw24457step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24457step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw24457step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw24458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw24458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw24459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw24460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw24460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw24461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw24461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, -1, 1], ![2, 0, -2]]
def raw24462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, -1, 1], ![2, 0, -2]]
def raw24462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1], ![1, 1, -2]]
def raw24463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1], ![1, 1, -2]]
def raw24463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw24463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24464 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![-1, 1], ![2, -2]]
def raw24464Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24464step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![-1, 1], ![2, -2]]
def raw24464step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24464step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw24464step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24464step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw24464step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24465step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24465step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24469step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24469step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24469step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24470step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24470step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24471step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24471step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24471step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24472step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24472step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24473step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24474step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24474step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24477step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24477step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24477step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24478step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw24481step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24481step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw24481step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw24482step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw24482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24484step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24484step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw24485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw24485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24485step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24485step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw24490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24492step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw24495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24499step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw24500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24504step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24505step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24506step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24508step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw24510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw24510step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw24511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw24512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24513step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw24513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24514step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw24515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw24515step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24516step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24517step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24517step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24517step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24517step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24517step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24518step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24518step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24518step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24518step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24519step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24519step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24519step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24519step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24520step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw24520step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24520step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24520step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24520step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24521step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24521step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24521step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24521step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24522step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24522step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24522step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24523step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24523step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24523step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24523step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24524step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24524step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24524step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24525Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw24525step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24525step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24525step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24526step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw24526step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24526step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24526step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24526step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24527Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw24527step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24527step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24527step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24527step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24528step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw24528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24528step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24528step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24528step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24529Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24529step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw24529step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24529step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24529step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24529step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24530step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw24530step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24530step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24530step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24530step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24531Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24531step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw24531step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24531step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24531step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24531step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24532Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw24532step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24532step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24532step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24532step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24533Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24533step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw24533step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw24533step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24533step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw24533step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24534Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24534step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw24534step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24534step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24534step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24534step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24534step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24535Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24535step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24535step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24535step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24535step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24535step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24535step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24536Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24536step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw24536step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24536step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24536step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24536step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24536step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24537Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw24537step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24537step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24537step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24538Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24538step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw24538step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24538step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw24538step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24538step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw24538step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24539Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24539step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw24539step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24539step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24539step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24539step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw24540Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw24540step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24540step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24540step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24540step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24541Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24541step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw24541step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24541step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24541step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24541step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24542Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw24542step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24542step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24542step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24543Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24543step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw24543step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw24543step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24543step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw24543step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24544Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24544step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw24544step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24544step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24544step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24544step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw24545Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw24545step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw24545step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24545step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24545step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24545step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24546step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24549step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24550step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24552 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw24552Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24552step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw24552step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24558step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24558step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24559step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24559step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24560step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24560step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24560step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw24561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24561step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24561step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24561step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24561step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24562step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24562step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24563step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24564step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw24565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24566step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24566step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24567step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24568step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24568step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, -1, -1]]
def raw24569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24569step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24569step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24569step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24570step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24570step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24571step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24572step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24572step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24573step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24573step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24573step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24574step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24575step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24575step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical192
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24576step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24576step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24577step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24577step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24577step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24577step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -2, -1]]
def raw24578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24578step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24578step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24578step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24578step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24578step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw24579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw24579step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw24583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24583step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24583step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24584step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24584step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24586step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw24587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24587step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24587step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, -1, -1]]
def raw24591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24591step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24591step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24591step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24591step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24592step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24592step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24594step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24595step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24595step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24595step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24596step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24598step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24598step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24599step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24599step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24599step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24599step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24599step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -2, -1]]
def raw24600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24600step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24600step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24600step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24600step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24605 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24605step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24607 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24607step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24609 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24609step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24609step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24612 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24612step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24612step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24613 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24613step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24613step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24620 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24620Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24620step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24621 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24621Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24621step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24621step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24622 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24622step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24623 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24623step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24624 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24624step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24625 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24625step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24626 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24626step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24627 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24627step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24628 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24629 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24630 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24630step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24630step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24630step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24631 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24631step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24632 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24632step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24633 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24633step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24634 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24634step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24634step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24634step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24635 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24635step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24636 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24636step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24637 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24638 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24639 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24640 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24641 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24641step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24642 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24643 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24644 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24644step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24645 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24646 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24647 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24648 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24649 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24655step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24660step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24661step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24661step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24661step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24662step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24662step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24665step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24666step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24670step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24671step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw24674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw24674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw24675step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw24675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw24676step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24676step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw24676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw24677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw24679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24680step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24681step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24683step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24683step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw24683step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24684step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw24684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24686step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24693step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24693step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24693step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24698step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24700step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24702Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24702step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24703step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24703step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical193
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw24704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw24704step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24705step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw24705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw24706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24707step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw24707step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24708step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24708step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw24709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24709step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24709step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24710step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24710step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24710step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24710step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24711step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24711step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24711step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24711step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24711step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw24712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24712step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24712step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24713step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24713step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24713step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24713step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24713step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24713step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24713step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24713step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24714step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw24714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24714step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24714step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw24715step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24715step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24715step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24716step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24716step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw24717step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24717step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24717step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24718step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw24719step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24719step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24720step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24720step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24721step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24722step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24722step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24722step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24723step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24723step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24723step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24723step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24723step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw24724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24724step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24724step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24725step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24725step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24725step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24726step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24726step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24726step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24726step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw24727step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw24727step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24727step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw24727step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24728step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw24728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24728step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24728step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24728step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw24729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24729step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24729step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw24730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24730step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw24731step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24731step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw24732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw24732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24732step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw24732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw24733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24733step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24733step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw24734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw24734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24734step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24734step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24734step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw24735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24735step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24735step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw24736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24736step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw24737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw24737step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24737step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw24737step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw24738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24738step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24738step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24738step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw24739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24739step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24739step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24739step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24739step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw24739step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24739step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24739step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24739step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24739step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24742step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw24745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24746 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]
def raw24746Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24746step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]
def raw24746step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24746step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw24746step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw24751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24754step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw24755step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw24756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24757step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24757step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24758step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24759step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24759step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24760step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24760step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24761step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24762step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24762step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24763step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24763step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24764step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24764step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24764step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24764step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24764step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24764step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24765step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24765step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24767step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24767step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24768step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24768step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24769step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24770step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24770step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24771step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24771step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24772step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24772step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24773step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24774step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24775step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24775step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24775step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw24776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw24776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24776step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24776step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24777step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24777step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24778step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24778step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24779step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24780step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw24780step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24780step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw24780step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw24781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw24781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw24781step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw24781step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24782step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24784step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24784step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24792step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24793Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24794Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24794step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24794step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24795step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24796Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24796step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24797Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24797step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24797step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24798Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24799Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24799step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24800Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24800step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24801Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24801step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24801step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24802step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24804step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24805step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24805step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24805step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw24806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw24806step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24807step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24809step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24810step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24810step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw24810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw24811Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw24811step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw24811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24815 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24815step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24815step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24815step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24818 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24818step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 1, -3]]
def raw24830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 1, -3]]
def raw24830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 2, -3]]
def raw24831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 2, -3]]
def raw24831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw24831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical194
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24832 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![3, -3]]
def raw24832Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24832step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![-1, 1], ![3, -3]]
def raw24832step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24832step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw24832step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24832step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24832step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24833step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24838step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24839 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw24839Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24839step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw24839step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24839step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw24839step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw24843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw24843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2]]
def raw24848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]
def raw24849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]
def raw24849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24850 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![2, -2], ![0, 0], ![2, -2]]
def raw24850Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24850step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![2, -2], ![2, -2]]
def raw24850step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24850step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw24850step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw24855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw24855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24857 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw24857Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24857step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw24857step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![0, 0, 0], ![2, 1, -3]]
def raw24872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]
def raw24873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]
def raw24873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24874 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![1, -1], ![0, 0], ![3, -3]]
def raw24874Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24874step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![1, -1], ![3, -3]]
def raw24874step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24874step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]
def raw24874step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24874step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw24874step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24874step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw24874step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24881 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw24881Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24881step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24881step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw24885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2]]
def raw24890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]
def raw24891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24892 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![0, 0], ![2, -2]]
def raw24892Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24892step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw24892step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24892step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw24892step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24892step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw24892step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw24897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24899 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24899Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 1, -3]]
def raw24913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]
def raw24914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24915 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![3, -3]]
def raw24915Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24915step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw24915step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24915step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw24915step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24915step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24915step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw24921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24922 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1], ![1, -1], ![-1, 1]]
def raw24922Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24922step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1], ![1, -1], ![-1, 1]]
def raw24922step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24922step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24922step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw24926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw24926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24927step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24928step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24930step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw24931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw24931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw24932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw24932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw24932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24933 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1], ![-1, 1], ![1, -1]]
def raw24933Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24933step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1], ![-1, 1], ![1, -1]]
def raw24933step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24933step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24933step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw24934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw24934step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24934step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw24935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw24936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw24936step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw24937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw24937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw24937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24938Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24938step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24943step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24944 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]
def raw24944Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24944step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![1, -1], ![1, -1]]
def raw24944step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24944step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24944step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24945Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24945step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24946step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw24948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24948step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24950Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24950step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24951step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw24952step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw24953Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24953step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw24954Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24955 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![1, -1], ![0, 0], ![1, -1]]
def raw24955Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24955step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![1, -1], ![1, -1]]
def raw24955step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24955step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24955step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24956Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24956step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24957Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24958Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24958step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24959Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24959step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw24960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24960Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24960step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw24961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw24961step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24962 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![0, 0], ![0, 0], ![2, -2]]
def raw24962Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24962step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![0, 0], ![2, -2]]
def raw24962step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24962step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![2, -2]]
def raw24962step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24962step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw24962step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw24967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw24968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24969 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]
def raw24969Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24969step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw24969step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw24973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24974Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24977Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw24978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw24979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw24979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24980 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]
def raw24980Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24980step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw24980step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw24981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw24982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw24983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw24984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw24984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24987step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24988step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw24989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw24989step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw24990step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24991 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2], ![1, -1], ![-1, 1]]
def raw24991Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24991step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2], ![1, -1], ![-1, 1]]
def raw24991step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24991step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24991step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24992Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24992step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24993step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw24995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw24995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24998step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw25000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw25000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw25001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw25001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25002 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2], ![-1, 1], ![1, -1]]
def raw25002Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25002step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2], ![-1, 1], ![1, -1]]
def raw25002step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25002step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw25002step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25003step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25006step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25006step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25007step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25010step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25011step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25012step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25013step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25014step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25015step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25015step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25016step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25017step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25024step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25025Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25025step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25025step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25025step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25025step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25025step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25025step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25026Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25026step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25026step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25026step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25026step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25027Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25027step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25027step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25027step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25027step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25027step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25028Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25028step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25028step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25028step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25028step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25028step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25029Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25029step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25029step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25029step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25029step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25029step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25030Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25030step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25030step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25030step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25030step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


