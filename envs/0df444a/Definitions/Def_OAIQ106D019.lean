-- Prove2me | Definitions.Def_OAIQ106D019
-- name    : OAIQ106D019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:07:10.449104+00:00
-- url     : https://prove2.me/theorems/b87662b4-55b0-4948-9699-4e0757bc1435
-- title:
--   Definitions bundle OAIQ106D019 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7678 declarations of OpenAI's Lean: 7678 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw21629Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21629step0`, `OAI.MUB6.Certificate.MixedSemantics.raw21629step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2162Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2162step0`, `OAI.MUB6.Certificate.MixedSemantics.raw2162step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2162step1`, `OAI.MUB6.Certificate.MixedSemantics.raw2162step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2162step2`, `OAI.MUB6.Certificate.MixedSemantics.raw2162step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2163`, `OAI.MUB6.Certificate.MixedSemantics.raw21630`, `OAI.MUB6.Certificate.MixedSemantics.raw21630Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21630step0`, `OAI.MUB6.Certificate.MixedSemantics.raw21630step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21630step1`, `OAI.MUB6.Certificate.MixedSemantics.raw21630step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21631`, `OAI.MUB6.Certificate.MixedSemantics.raw21631Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21631step0`, `OAI.MUB6.Certificate.MixedSemantics.raw21631step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21631step1`, `OAI.MUB6.Certificate.MixedSemantics.raw21631step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21631step2`, `OAI.MUB6.Certificate.MixedSemantics.raw21631step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21632`, `OAI.MUB6.Certificate.MixedSemantics.raw21632Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21632step0`, `OAI.MUB6.Certificate.MixedSemantics.raw21632step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21632step1`, `OAI.MUB6.Certificate.MixedSemantics.raw21632step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21633`, `OAI.MUB6.Certificate.MixedSemantics.raw21633Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21633step0`, `OAI.MUB6.Certificate.MixedSemantics.raw21633step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21633step1`, `OAI.MUB6.Certificate.MixedSemantics.raw21633step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21633step2`, `OAI.MUB6.Certificate.MixedSemantics.raw21633step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21634` and 7638 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical1`, `MutuallyUnbiased_MixedSemantics_Canonical16`, `MutuallyUnbiased_MixedSemantics_Canonical168`, `MutuallyUnbiased_MixedSemantics_Canonical169`, `MutuallyUnbiased_MixedSemantics_Canonical17`, `MutuallyUnbiased_MixedSemantics_Canonical170`, `MutuallyUnbiased_MixedSemantics_Canonical171`, `MutuallyUnbiased_MixedSemantics_Canonical172`, `MutuallyUnbiased_MixedSemantics_Canonical173`, `MutuallyUnbiased_MixedSemantics_Canonical174`, `MutuallyUnbiased_MixedSemantics_Canonical175`, `MutuallyUnbiased_MixedSemantics_Canonical176`, `MutuallyUnbiased_MixedSemantics_Canonical177`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1162`, `OAI.MUB6.Certificate.MixedSemantics.sound1163`, `OAI.MUB6.Certificate.MixedSemantics.sound2532`, `OAI.MUB6.Certificate.MixedSemantics.sound2570`, `OAI.MUB6.Certificate.MixedSemantics.sound2572`, `OAI.MUB6.Certificate.MixedSemantics.sound2574`, `OAI.MUB6.Certificate.MixedSemantics.sound2576`, `OAI.MUB6.Certificate.MixedSemantics.sound5167`, `OAI.MUB6.Certificate.MixedSemantics.sound5168`, `OAI.MUB6.Certificate.MixedSemantics.sound5169`, `OAI.MUB6.Certificate.MixedSemantics.sound5171`, `OAI.MUB6.Certificate.MixedSemantics.sound5172`, `OAI.MUB6.Certificate.MixedSemantics.sound5174`, `OAI.MUB6.Certificate.MixedSemantics.sound5176`, `OAI.MUB6.Certificate.MixedSemantics.sound5177`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound74`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound75`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound77`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound79`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound94`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound95`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1780`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero733`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero863`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1205`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1227`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1232`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1271`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1422`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1428`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1436`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1561`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1741`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1744`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1882`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2045`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2063`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound426`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound446`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound503`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound536`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound612`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound620`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound642`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound682`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound686`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound693`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound728`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound744`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound745`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound974`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990`.
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

def raw21Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw21step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw22 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]

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

def raw216Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw216step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw217 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw217Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw217step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw217step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw220 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw220step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw221 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw221Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw221step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw222 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw222step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw223 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw223Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw223step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw223step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw224 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw224Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw224step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw224step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw225 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw225Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw225step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw225step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw226 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2162Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw2162step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2162step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2162step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2162step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2163 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2163step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2163step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2163step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2164 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2164Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2164step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2165 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2165Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw2165step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2165step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2165step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2165step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2166 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2166step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2166step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2167 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2167Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2167step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2168 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2168Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2168step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2168step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2168step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2168step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2169 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2]]
def raw2169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw2169step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw2169step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2170 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2]]
def raw2170Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw2170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2171 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2]]
def raw2171Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw2171step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2171step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2172 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw2172step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2172step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw2172step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2173 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2173Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2174 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2174Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw2174step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2174step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw2174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2174step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw2174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2175 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw2175step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw2175step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw21629Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw21629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw21630Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw21630step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw21630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21631 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21631Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw21631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21631step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw21631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical169
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw21632 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21632Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw21632step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21633 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw21633Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw21633step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw21633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21634step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21634step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21634step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw21634step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21636step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21637step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21637step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21638step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21638step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21638step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw21638step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21639step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21640step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21642step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21642step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw21642step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21643step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21645step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21646step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw21646step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21647step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21647step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw21647step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21648step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21648step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21649step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21649step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21651step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw21651step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21654step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw21655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw21655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw21655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21655step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw21655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21656Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21656step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21656step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21656step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21656step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21656step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21656step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21656step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21657Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21657step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21657step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21657step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21657step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21657step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21657step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21657step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21658Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21658step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21658step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21658step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21658step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21658step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21658step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21658step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21659Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21659step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21659step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21659step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw21659step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21659step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw21659step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21659step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw21659step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21659step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw21659step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21660Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21660step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21660step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21660step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw21660step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21660step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw21660step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21660step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw21660step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21660step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw21660step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21661Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21661step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21661step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21661step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21661step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21661step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21661step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21661step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21662Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21662step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21662step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21662step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21662step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21662step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21663Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21663step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21663step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21663step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21663step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21663step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21663step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21664Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21664step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21664step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw21664step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21664step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw21664step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21664step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw21664step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21665Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21665step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21665step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw21665step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21665step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21665step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21665step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21665step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21666Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21666step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21666step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21666step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21666step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21666step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21666step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21666step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21666step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21667Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21667step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21667step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21667step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21667step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21667step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21668Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21668step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21668step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21668step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21668step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21668step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21669Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21669step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21669step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw21669step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21669step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw21669step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21669step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw21669step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21670Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21670step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21670step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21670step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw21670step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21670step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21670step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21670step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21670step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21671Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21671step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21671step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21671step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21671step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21671step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21671step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21671step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21671step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21672Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21672step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21672step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21672step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21672step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21672step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21672step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21673Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21673step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21673step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21673step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21673step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21673step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21674Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21674step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21674step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21674step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw21674step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21674step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw21674step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21674step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw21674step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21675Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21675step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21675step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw21675step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21675step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21675step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21675step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21675step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21676Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21676step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21676step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21676step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw21676step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21676step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -2, 3], ![-2, 0, 2]]
def raw21676step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21676step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]
def raw21676step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21676step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]
def raw21676step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21677Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21677step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21677step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw21677step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21677step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw21677step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21677step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw21677step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21678Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21678step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21678step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21678step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw21678step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21678step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw21678step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21678step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw21678step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21679Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21679step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21679step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw21679step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21679step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw21679step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21679step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw21679step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw21680Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw21680step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw21680step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21680step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![2, -1, -1]]
def raw21680step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21680step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw21680step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21680step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw21680step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21680step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw21680step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21681Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21681step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21681step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21681step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw21681step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21681step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -3, 4], ![-2, 1, 1]]
def raw21681step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21681step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def raw21681step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21681step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def raw21681step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21682Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21682step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21682step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -3, 4], ![-2, 1, 1]]
def raw21682step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21682step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw21682step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21682step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw21682step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21683Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21683step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21683step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -3, 4], ![-2, 1, 1]]
def raw21683step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw21683step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21683step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw21683step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21684Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21684step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21684step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -3, 4], ![-2, 1, 1]]
def raw21684step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21684step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw21684step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21684step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw21684step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw21685Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw21685step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw21685step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21685step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw21685step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21685step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw21685step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21685step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw21685step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21686Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21686step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21688step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21690step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21690step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21691step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21692step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21692step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21693step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21693step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21693step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21694step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21694step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21694step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21694step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21695step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21695step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21696step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21696step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21697step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21697step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21697step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21698step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21698step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21699step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21700step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21700step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21701step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21701step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21701step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21701step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21702step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21702step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 4, 1], ![2, -3, 1], ![3, -1, -2]]
def raw21702step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21702step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw21702step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21702step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw21702step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21703step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21703step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw21703step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21703step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw21703step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw21704step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21704step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw21704step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw21705step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21705step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw21705step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21706step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21706step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![4, -2, -2]]
def raw21706step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21706step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw21706step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21706step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw21706step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21707step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21707step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21707step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21708step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21708step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21708step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21709step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21709step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21709step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw21710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw21710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw21710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21710step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![4, -2, -2]]
def raw21710step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21710step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21710step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21710step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21710step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21736 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21736step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21736step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21736step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21736step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21740 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21740step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21740step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21740step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21740step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21740step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21740step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21740step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21744 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21744step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21744step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![2, -3, 1], ![-2, -1, 3]]
def raw21744step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21744step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -2, 3], ![-3, 2, 1]]
def raw21744step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21744step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw21744step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21744step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw21744step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21750 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21750step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21750step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21750step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21750step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21750step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21751 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21751step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21751step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21751step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21751step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21751step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2176 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2176Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2177 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2177Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw2177step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw2177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2177step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw2177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2178 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw2178Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw2178step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw2178step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2179 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw2179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw2179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2180 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw2180Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw2180step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw2180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw2180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2181 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2181step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2181step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2182 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2182Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2183 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2183Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw2183step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw2183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2183step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw2183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2184 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw2184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw2184step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw2184step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2185 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw2185Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw2185step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2186 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw2186Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-2, 2, 0]]
def raw2186step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]
def raw2186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]
def raw2186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2187 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2187step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2187step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2188 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2188Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2188step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2189 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2189Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2189step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2189step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2189step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2190 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2190step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2190step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2191 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2192 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2192Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw2192step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2193 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2193step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2194 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2195 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2195Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2195step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2195step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2195step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2196 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2196step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2196step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2197 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2197step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2198 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2198Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw2198step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw2198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw2198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2199 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2199step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2200 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2201 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2201Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2201step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2201step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2201step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2202 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2202step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2202step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2203 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2204 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2204Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw2204step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw2204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw2204step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2205 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 3, -2]]
def raw2205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2205step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw2205step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw2205step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2206 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 3, -2]]
def raw2206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2206step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw2206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2207 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 3, -2]]
def raw2207Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2207step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]
def raw2207step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]
def raw2207step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2208 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2208step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2208step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2209 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2210 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2210Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1]]
def raw2210step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw2210step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw2210step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2211 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![-2, 3, -1]]
def raw2211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2211step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw2211step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw2211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2212 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![-2, 3, -1]]
def raw2212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2212step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw2212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2213 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![-2, 3, -1]]
def raw2213Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2213step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]
def raw2213step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]
def raw2213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2214 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 2, 0], ![0, 2, -2]]
def raw2214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2214step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2214step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2215 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 2, 0], ![0, 2, -2]]
def raw2215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2215step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2216 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 2, 0], ![0, 2, -2]]
def raw2216Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2216step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw2216step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]
def raw2216step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2216step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]
def raw2216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2217 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2217step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2217step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2218 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2218step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2219 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2219Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2219step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2219step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2219step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2219step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2219step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2219step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2220 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2220step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2220step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2221 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2222 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2222Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0]]
def raw2222step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw2222step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2222step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw2222step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2223 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw2223step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw2223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2224 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2224Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2224step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2225 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2225Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0]]
def raw2225step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw2225step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2225step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw2225step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2226 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw2226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2226step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2226step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2227 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw2227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2228 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw2228Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw2228step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2228step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2228step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2228step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2228step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2229 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw2229step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw2229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2230 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2231 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2231Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw2231step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2231step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2231step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2232 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw2232step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw2232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2233 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2233step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2234 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2234Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw2234step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw2234step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw2234step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2235 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]
def raw2235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2235step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw2235step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw2235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2236 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]
def raw2236Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2236step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw2236step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2237 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]
def raw2237Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2237step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw2237step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2237step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw2237step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2237step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw2237step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2247 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2247step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2248 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2248Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2248step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2249 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2249Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2249step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2249step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2249step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2250 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2250step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2251 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2251Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2251step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2252 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2252Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw2252step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2252step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2252step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2253 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2253step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2254 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2254Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2254step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2255 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2255Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2255step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2255step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2256 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 1, -2], ![0, 2, -2]]
def raw2256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2256step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw2256step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2256step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw2256step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2257 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 1, -2], ![0, 2, -2]]
def raw2257Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2257step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw2257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2258 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 1, -2], ![0, 2, -2]]
def raw2258Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2258step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw2258step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2258step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2258step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2259 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2259step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2260 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2260Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2260step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2261 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2261Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw2261step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2261step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2261step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2262 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2262step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2263 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2263Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2263step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2264 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2264Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2264step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2264step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2264step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2264step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2265 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 2, -2]]
def raw2265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2265step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2266 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 2, -2]]
def raw2266Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2266step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2267 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 2, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw21771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21772step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21774step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21775step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![2, 0, -2]]
def raw21775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21775step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw21775step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw21775step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw21775step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21777step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21778step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21779step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21781step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21783step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21784step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21784step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21784step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21786step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21786step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21789step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21789step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21789step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21790step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21790step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21791step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw21791step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21795step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw21795step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21796step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21796step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw21796step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21797step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21799step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21800step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21800step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21800step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21800step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21801step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21801step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21801step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21801step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21801step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21801step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21801step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21802step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21802step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21802step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21802step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21802step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21802step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21802step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21803step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21803step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21803step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21803step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21803step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21803step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21803step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21803step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21804step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21804step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21804step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21804step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21804step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-2, -1, 3]]
def raw21804step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21804step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw21804step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21804step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw21804step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21805step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21805step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21805step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![2, 0, -2]]
def raw21805step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21805step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw21805step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21806step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21806step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21806step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21806step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21806step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21806step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21806step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21806step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21807step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21807step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21807step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21807step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21807step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21807step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21808step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21808step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21808step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21808step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21809Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21809step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21809step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21809step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21809step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21809step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21809step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21809step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21810Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21810step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21810step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw21810step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21810step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21810step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21810step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21810step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21811Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21811step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21811step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21811step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21811step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21811step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21811step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21811step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21811step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21811step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21812Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21812step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21812step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21812step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21812step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21813Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21813step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21813step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21813step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21813step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21813step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21813step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21814step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21814step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21814step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21814step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21814step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21814step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21814step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21814step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21815step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21815step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21815step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21815step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw21815step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21815step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21815step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21815step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21815step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21816step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21816step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21816step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21816step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21816step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21816step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21816step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21816step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21816step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21817step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21817step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21817step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21817step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21817step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21818step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21818step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21818step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21818step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21818step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21819step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21819step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21819step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21819step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21819step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21819step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21819step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21819step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21819step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21820Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21820step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21820step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21820step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw21820step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21820step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21820step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21820step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21820step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21821Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21821step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21821step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21821step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw21821step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21821step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -1, 2], ![-2, -1, 3]]
def raw21821step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21821step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw21821step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21821step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw21821step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21822Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21822step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21822step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21822step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21822step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw21822step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21822step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21822step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21822step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21822step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21823Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21823step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21823step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21823step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw21823step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21823step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21823step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21823step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21823step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21824Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21824step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21824step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21824step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw21824step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21824step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21824step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21824step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21824step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21825Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21825step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21825step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21825step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw21825step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21825step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw21825step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21825step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw21825step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21825step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw21825step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21826Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21826step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21826step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21826step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21826step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw21826step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21826step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-2, -2, 4]]
def raw21826step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21826step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw21826step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21826step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw21826step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21827Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21827step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21827step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21827step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw21827step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21827step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21827step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21827step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21827step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21828Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21828step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21828step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21828step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21828step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw21828step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21828step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21828step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21828step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21828step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21829Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21829step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21829step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21829step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw21829step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21829step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21829step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21829step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21829step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21830Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21830step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21830step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21830step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21830step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21830step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw21830step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21830step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw21830step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21830step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw21830step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21832step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21832step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21833step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21833step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21834step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw21834step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21834step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw21834step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21834step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21834step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21834step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21834step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21835step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21836step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21837step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21838step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21838step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21839step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21839step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21840step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21841step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21842step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21843step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21846step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21847step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw21847step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21848step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21849step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21849step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21849step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21850step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21850step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21850step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21851step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw21851step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21852step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21852step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21852step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![4, -1, -3]]
def raw21852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21852step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw21852step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21853Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21853step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21853step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21853step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21853step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21853step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21854Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21854step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21854step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21854step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21854step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21854step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21854step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21854step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21855Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21855step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21855step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21855step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21855step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21855step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21855step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21855step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21856Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21856step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21856step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21856step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21856step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw21856step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21856step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw21856step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21856step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21856step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21856step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21856step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21857Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21857step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21857step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21857step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21857step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21857step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21857step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21857step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21857step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21858Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21858step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21858step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21858step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21858step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21859Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21859step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21859step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21859step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21859step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21859step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21860Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21860step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21860step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21860step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw21860step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21860step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21860step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21860step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21860step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21861Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21861step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21861step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21861step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21861step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21861step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21861step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21861step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21862Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21862step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21862step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21862step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21862step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21862step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21863Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21863step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21863step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21863step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21863step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21863step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21864Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21864step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21864step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21864step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw21864step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21864step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21864step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21864step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21864step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21865Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21865step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21865step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21865step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21865step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21865step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21865step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21865step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21865step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21866Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21866step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21866step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21866step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21866step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21866step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21867Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21867step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21867step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21867step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21867step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21867step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21868Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21868step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21868step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw21868step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21868step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21868step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21868step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21868step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21869Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21869step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21869step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21869step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw21869step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21869step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-3, 0, 3]]
def raw21869step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21869step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw21869step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21869step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw21869step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21870Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21870step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21870step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw21870step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21870step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21870step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21870step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21870step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21871Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21871step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21871step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21871step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw21871step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21871step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21871step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21871step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21871step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21872Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21872step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21872step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21872step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw21872step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21872step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21872step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21872step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21872step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21873Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21873step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21873step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21873step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw21873step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21873step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw21873step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21873step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw21873step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21873step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw21873step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21874Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21874step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21874step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21874step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![4, -1, -3]]
def raw21874step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21874step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw21874step3Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21874step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -1, 4], ![3, 1, -4]]
def raw21874step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21874step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -1, 4], ![3, 1, -4]]
def raw21874step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21875step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw21875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21876step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21879step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw21879step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw21882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw21882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw21882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21882step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw21882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21887step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical171
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw21888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw21888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw21888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw21888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21890 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![-1, 1], ![3, -3], ![1, -1]]
def raw21890Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21890step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![3, -3], ![1, -1]]
def raw21890step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21890step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![3, -3], ![1, -1]]
def raw21890step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21890step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw21890step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw21891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw21892step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21893step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw21894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw21894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw21894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21898step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21901 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw21901Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21901step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw21901step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21901step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw21901step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw21906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw21906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw21906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw21909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw21909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw21909step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw21910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw21911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21918step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21918step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21918step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21919step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21919step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21920step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21920step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21920step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw21920step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw21920step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw21920step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21921step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21921step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21921step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21921step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21922step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21922step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21922step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw21922step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21922step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21922step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21922step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21922step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21923step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21925step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21926step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw21927step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21928step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21930step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21931step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw21932step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw21936step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21937step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21938step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw21944step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21944step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw21945step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21945step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21946step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21948step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21949step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21950step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21950step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21950step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw21950step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21951step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21951step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21951step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21951step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21951step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21952step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21952step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw21952step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21952step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21952step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21952step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21952step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21953step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21953step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21953step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21953step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21954step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21954step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21954step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21955step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21955step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21955step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21955step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21956step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21956step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21956step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21956step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21957step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21957step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21957step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21957step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21957step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21957step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21958step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21958step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21958step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21958step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21959step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21959step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21959step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21960step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21960step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21960step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21960step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21960step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21961step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21961step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21961step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21961step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21962step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21962step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21962step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21962step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21963Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21963step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21963step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21963step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21963step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21963step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21963step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21963step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21964Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21964step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21964step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21964step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21964step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21964step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21965Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21965step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21965step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21965step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21965step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21965step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21966Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21966step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21966step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21966step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21966step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21966step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21966step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21966step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21967Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21967step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21967step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21967step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21967step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21967step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21967step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21967step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21967step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21968Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21968step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21968step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21968step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw21968step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21968step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw21968step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21968step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw21968step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21969Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21969step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 0, 3]]
def raw21969step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21969step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21969step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21969step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21970Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21970step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 0, 3]]
def raw21970step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21970step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21970step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21970step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21971Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21971step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21971step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, -1, 2], ![-3, 0, 3]]
def raw21971step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21971step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21971step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21971step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21971step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21972Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21972step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21972step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw21972step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21972step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21972step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21972step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21973Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21973step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21973step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21973step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-3, -1, 4]]
def raw21973step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21973step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![3, 1, -4]]
def raw21973step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21973step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![3, 1, -4]]
def raw21973step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21974Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21974step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw21974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw21974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21975Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21975step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw21975step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw21975step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21976Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21976step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21976step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![3, 1, -4]]
def raw21976step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![3, 1, -4]]
def raw21976step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21977step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21977step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw21977step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21977step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw21977step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21980Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21980step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw21983step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21984 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![-1, 1], ![1, -1], ![3, -3]]
def raw21984Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21984step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![1, -1], ![3, -3]]
def raw21984step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21984step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw21984step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21991 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21991step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21991step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![0, -1, 1], ![0, -3, 3]]
def raw21991step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21991step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw21991step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw21991step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw21991step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw21991step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw21991step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21994 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw21994step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21994step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw21994step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21994step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw21994step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw22002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw22006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw22006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw22007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw22007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw22007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22008 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![0, 0], ![1, -1], ![0, 0]]
def raw22008Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22008step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![0, 0], ![1, -1]]
def raw22008step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22008step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]
def raw22008step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22008step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22008step2Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical172
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22016step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, 0, -2], ![2, -2, 0]]
def raw22020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22020step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22020step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw22021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22022 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![0, 0], ![2, -2], ![0, 0]]
def raw22022Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22022step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![0, 0], ![2, -2]]
def raw22022step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22022step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![2, -2]]
def raw22022step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22022step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw22022step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22023step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw22023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22024step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![3, -2, -1]]
def raw22024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw22025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw22026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw22027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw22027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![3, -2, -1]]
def raw22027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw22027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw22028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22029 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]
def raw22029Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22029step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![1, -1], ![1, -1]]
def raw22029step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22029step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]
def raw22029step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22029step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22029step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw22034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw22034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw22037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22040 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw22040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw22040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22040step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw22040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22040step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw22040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22040step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22040step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22041step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22044step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![3, -1, -2]]
def raw22045step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22045step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw22045step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22047 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]
def raw22047Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22047step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![0, 0], ![2, -2]]
def raw22047step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22047step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![2, -2]]
def raw22047step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22047step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw22047step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22048step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22048step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22048step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22049step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22050step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22051step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22051step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![3, -1, -2]]
def raw22051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22051step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]
def raw22051step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22052step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22052step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22056step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw22056step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22056step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22056step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22057 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw22057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22057step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22064 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]
def raw22064Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22064step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw22064step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw22065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw22066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw22067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw22068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw22070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22071 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]
def raw22071Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22071step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw22071step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22073step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22078 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]
def raw22078Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22078step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![2, -2]]
def raw22078step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22078step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22078step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22082step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw22083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw22083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22085 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw22085Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22085step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw22085step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22086step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22087step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22088step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw22089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw22089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22090step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22091step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22096 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw22096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw22096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw22096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw22101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22102step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22103 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]
def raw22103Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22103step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![2, -2]]
def raw22103step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22103step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22103step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22106Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22106step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw22107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22107step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22107step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22109Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22109step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22112Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22112step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw22112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22113 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22113step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw22113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22113step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22113step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw22114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]
def raw22115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw22116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw22117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw22118Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw22118step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw22118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw22119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22120 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw22120Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22120step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![2, -2], ![1, -1]]
def raw22120step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22120step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw22120step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22120step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22120step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22121Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw22121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw22122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw22123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw22124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw22125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw22125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, 0, -2], ![2, -1, -1]]
def raw22125step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22125step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22125step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw22126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22131step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22131step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22131step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22131step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22131step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22131step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22132step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22132step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22132step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22132step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22133step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22133step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22133step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22133step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22134step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22134step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw22134step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22134step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22134step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22134step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22134step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22135step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22135step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw22135step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22135step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22135step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22135step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22135step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22138step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22139step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22139step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22140step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22140step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22140step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw22140step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22140step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22144step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22153step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22155step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22155step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22156step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw22160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw22160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22160step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw22160step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22161Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22161step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22161step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22161step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22161step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22161step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22161step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22161step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22161step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22162Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22162step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22162step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22162step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22162step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22163Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22163step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22163step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22163step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22163step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22163step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22164step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22164step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22164step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw22164step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22164step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22164step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22164step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22164step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22165Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22165step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22165step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22165step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw22165step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22165step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22165step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22165step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22165step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22166step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22166step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22166step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22166step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22166step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22166step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22166step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22166step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22167Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22167step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22167step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22167step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22167step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22167step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22168step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22168step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22168step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22168step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22168step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22169Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22169step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22169step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22169step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22169step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22169step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22169step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22169step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22169step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22170step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22170step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22170step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22170step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22171Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22171step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22171step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22171step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22171step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22171step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22172step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22172step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22172step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22172step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22172step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22173Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22173step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22173step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22173step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22174step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw22174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22174step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22174step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22174step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22175step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw22175step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22175step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22175step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22175step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22176step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22176step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22176step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22176step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22176step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22177step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22177step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22177step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22178step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22178step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22178step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22179step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw22179step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22179step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22179step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22179step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22179step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw22180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22180step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22180step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22180step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22181step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22181step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw22181step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22181step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22181step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22181step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22181step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22182step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22182step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw22182step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22182step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw22182step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22182step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw22182step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22183step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw22183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22183step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22183step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22183step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22184step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw22184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22184step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22184step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22184step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22185step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22185step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22185step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22185step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22185step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22185step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22185step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22185step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22185step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22186step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22186step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw22186step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22186step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22186step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22186step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22186step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22187step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22187step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw22187step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22187step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw22187step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22187step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw22187step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw22188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22188step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22188step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22188step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw22189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22189step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22189step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22189step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw22190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw22190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22190step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw22190step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22190step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw22190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22190step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw22190step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22190step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw22190step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22191step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22192Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22192step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22192step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22195step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22196step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22196step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22197 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]
def raw22197Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22197step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![1, -1], ![2, -2]]
def raw22197step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22197step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22197step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22206step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22211 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22211step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22211step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22211step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22211step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22214 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22214step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22214step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22214step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22214step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22216step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22216step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22216step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22216step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22216step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22216step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22217 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22217step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22217step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22217step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22217step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22218 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22218step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22218step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22218step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22218step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22218step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw22221step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22221step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw22221step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22221step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw22221step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw22222step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22222step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22222step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22222step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw22223step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22223step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22223step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22223step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![3, 0, -3]]
def raw22224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22224step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw22224step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22224step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-3, 0, 3]]
def raw22224step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22224step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw22224step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22224step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw22224step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw22225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw22225step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22225step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22225step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22225step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22225step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw22226step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw22227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw22228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22229step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![3, 0, -3]]
def raw22229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22229step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![3, 0, -3]]
def raw22229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22229step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw22229step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw22229step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw22229step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw22230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22230step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw22230step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22230step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22230step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22230step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22230step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw22235step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22235step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22235step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22235step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw22240step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22240step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22240step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22240step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22240step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw22246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw22247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw22248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw22249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw22250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw22250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![4, -1, -3]]
def raw22250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22250step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw22250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22258step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw22258step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22258step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22258step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22258step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22258step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22259step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw22259step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22259step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22259step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22259step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22259step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw22260step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22260step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22260step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22260step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22260step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22261step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22261step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw22261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22261step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-2, 2, 0], ![-2, -1, 3]]
def raw22261step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22261step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw22261step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22261step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw22261step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22262step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw22262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22262step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-2, 1, 1], ![-2, 0, 2]]
def raw22262step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22262step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22262step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22262step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22262step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22264step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22266step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22266step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22266step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw22266step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22266step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22266step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22266step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22266step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22267step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22267step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw22267step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22267step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22267step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22267step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22267step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22268step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22271step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw22271step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22271step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22271step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22271step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22271step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical174
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22272step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22272step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22272step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw22272step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22272step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22272step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22272step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22272step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22273step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22273step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22276step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22276step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22276step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw22276step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22276step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22276step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22276step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22276step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22277step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw22277step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22277step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22277step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22277step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22277step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22278step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 0, -2], ![3, -1, -2]]
def raw22278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22279step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22280step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22282step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, 0, -2], ![2, 0, -2]]
def raw22282step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22282step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw22282step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw22282step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw22282step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22283step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw22283step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -2, -2]]
def raw22287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -2, -2]]
def raw22287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22287step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 2, -2], ![4, -2, -2]]
def raw22287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22287step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw22287step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22288step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22288step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22288step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22288step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22288step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22288step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22288step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22288step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22289 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22289step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22289step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22289step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22289step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22290 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22290step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22290step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22290step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22290step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22291step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22291step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22291step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22291step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22291step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22291step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22291step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22292 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22292step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22292step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22292step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22292step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22293 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22293step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22293step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22293step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22294step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22294step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22294step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -3, 1], ![-1, -2, 3]]
def raw22294step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22294step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![-2, -1, 3], ![-3, 2, 1]]
def raw22294step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22294step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw22294step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22294step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw22294step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22295 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22295step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw22295step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22295step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22295step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22295step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22295step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22296 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22296step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22296step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw22296step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22296step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22296step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22296step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22296step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22297 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw22297step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22297step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22297step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22297step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22297step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22298step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22298step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -2, 1], ![0, -3, 3]]
def raw22298step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22298step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![-2, 1, 1], ![-3, 0, 3]]
def raw22298step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22298step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -1, -1], ![3, 0, -3]]
def raw22298step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22298step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -1, -1], ![3, 0, -3]]
def raw22298step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22299 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22299step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw22299step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22299step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw22299step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22299step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw22299step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22300 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22300step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22300step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw22300step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22300step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw22300step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22300step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw22300step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22301step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22301step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]
def raw22301step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22302step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![1, -1], ![3, -3]]
def raw22302step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22302step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22302step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22303step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![1, -1], ![3, -3]]
def raw22303step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22303step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22303step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22304step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22304step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]
def raw22304step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22305step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22305step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22305step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22306step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![1, -1], ![3, -3]]
def raw22306step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22306step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22306step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22307step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22307step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]
def raw22307step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22308step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22308step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22308step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22309Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22309step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22309step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22309step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22310Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22310step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22310step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22310step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 5, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22310step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22310step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]
def raw22310step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22311Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22311step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22311step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22311step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22311step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw22311step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22312Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22312step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22312step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22312step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw22312step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22313Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22313step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22313step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22313step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw22313step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22314step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22317step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw22318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw22318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw22318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22318step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22319Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22319step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw22321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw22321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22321step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw22321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22321step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw22321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw22322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw22322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw22322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22323 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22323step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22323step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22323step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22323step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22326 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22326step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22326step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22326step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22329 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![0, 0], ![-2, 2], ![-2, 2]]
def raw22329Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22329step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![-2, 2], ![-2, 2]]
def raw22329step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22329step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![-2, 2], ![-2, 2]]
def raw22329step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22329step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-2, 2], ![-2, 2]]
def raw22329step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22329step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw22329step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22330 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw22330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw22330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22331 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw22331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw22331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22332 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22332step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22332step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22332step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22333 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22333step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22333step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22333step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22334 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22334step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22334step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22335 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22336 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22336step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22336step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22337 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22337step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22337step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22338 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22338step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22338step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22338step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22339 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22339step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22340 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22341 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22341step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22341step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22341step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22341step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22341step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22355step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22359step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22361 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22362 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22362step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22362step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22362step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22363 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw22363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw22363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw22363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22364 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22368 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22368step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22369 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22370 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22371 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22371step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22371step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22371step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22372 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw22372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw22372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22373 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22374 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22374step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22374step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22375 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22375step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw22382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw22382step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw22382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw22383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw22383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw22383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22384 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-2, 2], ![2, -2], ![2, -2]]
def raw22384Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22384step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![2, -2]]
def raw22384step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22384step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw22384step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22384step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw22384step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22392step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22393Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22393step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 1, -3]]
def raw22396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 1, -3]]
def raw22396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, -3, 0], ![2, 1, -3]]
def raw22396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22396step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw22396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22398 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![0, 0], ![3, -3]]
def raw22398Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22398step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]
def raw22398step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22398step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]
def raw22398step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22398step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw22398step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22398step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw22398step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22398step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw22398step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22399step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, 0, -2], ![2, -3, 1]]
def raw22399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22399step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw22400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw22403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw22403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw22403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw22404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw22404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, 0, -2], ![1, -2, 1]]
def raw22404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22405 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![2, -2], ![-1, 1]]
def raw22405Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22405step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![2, -2], ![-1, 1]]
def raw22405step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22405step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]
def raw22405step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22405step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw22405step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22406 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw22406step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22407 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22407step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22407step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22407step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22407step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22408 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22409 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22410 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22410step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw22410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22410step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22410step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22411 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22411step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22411step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22412 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22412step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22412step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 0, 2], ![1, -3, 2]]
def raw22412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22412step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw22412step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22412step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw22412step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22413 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22413step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22413step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw22413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22414 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22414step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22414step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw22414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22415 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22415step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 1, 2], ![1, -3, 2]]
def raw22415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22415step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw22415step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22416 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22416step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 0, 2], ![0, -2, 2]]
def raw22416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22416step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -2, 2], ![-2, 0, 2]]
def raw22416step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22416step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]
def raw22416step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22417 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22417step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw22417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22417step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22417step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22418 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22418step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22418step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -2, 0], ![2, 2, -4]]
def raw22418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22419 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw22419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22420 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw22420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22421 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22421step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22421step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22422 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22423 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22423step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, 0, -2]]
def raw22428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0], ![2, 0, -2]]
def raw22428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw22431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw22431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22431step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22432 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22432step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22433 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22434 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw22434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22434step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22435 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22439 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22439step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw22444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw22444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw22449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw22449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22450 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22451 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22451step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22452 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22453 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22454 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22455 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22455step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, -1, 2], ![-1, -1, 2]]
def raw22455step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22455step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]
def raw22455step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22456 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw22458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw22461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw22461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw22461step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw22462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw22462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22463 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-2, 2], ![2, -2], ![1, -1]]
def raw22463Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22463step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![2, -2], ![1, -1]]
def raw22463step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22463step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw22463step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw22468step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22470 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw22470Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22470step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw22470step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22471step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22471step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22471step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22471step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22472step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22472step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22473step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22474step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22474step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22474step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22474step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22474step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22475step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22475step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22475step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22475step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22476step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22476step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22476step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22477step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22477step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22477step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22478step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22478step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22478step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22478step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22479step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22479step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22479step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22479step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22480step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22480step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22480step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22481step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22481step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22481step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22482step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![3, -3, 0], ![2, 0, -2]]
def raw22482step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22482step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw22482step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22482step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw22482step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22483step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22483step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22483step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22483step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22484step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22484step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22484step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22484step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22484step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22485step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22485step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22485step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22485step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22485step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw22486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw22486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw22486step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22486step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![3, -3, 0], ![1, 1, -2]]
def raw22486step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22486step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw22486step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22486step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw22486step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22487step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22487step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22487step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22488step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22488step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22489step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22489step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22490step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22490step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22490step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22491step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22493step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22493step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22493step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22494step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22494step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22497step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22497step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22498step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22498step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22498step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22499step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22501step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22501step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22501step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![3, -3, 0], ![2, 0, -2]]
def raw22501step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22501step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw22501step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22502step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22502step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22502step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22503step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22503step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22504step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22504step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22504step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22504step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw22505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw22505step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw22505step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22505step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![3, -3, 0], ![1, 1, -2]]
def raw22505step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22505step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw22505step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22506 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22506step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22506step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22506step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22506step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22506step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22506step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22507 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22507Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22507step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22507step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22507step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22507step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22507step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22507step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22507step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22508 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22508step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22508step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22508step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22508step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22508step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22508step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22508step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22509 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22509step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22509step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22509step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-3, 1, 2], ![0, -2, 2]]
def raw22509step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22509step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw22509step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22509step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw22509step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22510 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22510step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22510step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22510step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 0, 2], ![-1, -1, 2]]
def raw22510step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22510step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22510step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22510step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22510step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22511 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22511step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22511step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22511step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22511step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22511step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22512 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22512step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22512step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22512step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22512step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22513 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22513step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22513step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22514 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22514step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22514step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22514step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22514step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22515 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22515step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22515step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22515step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22515step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22515step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22516 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22516step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22516step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22516step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22516step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22516step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22516step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22517 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22517step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22517step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22517step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22518 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22518step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22518step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22518step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22519 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22519step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22519step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22519step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22519step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22520 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22520step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22520step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22520step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22520step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22521 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22521step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22521step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22521step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22521step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22522 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22522step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22522step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22522step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22523 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22523step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22523step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22523step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22524 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22524step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22524step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22524step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22525 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22525step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22525step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22525step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22525step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22526 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22526step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22526step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, -1, 2], ![0, -2, 2]]
def raw22526step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22526step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22526step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22526step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22526step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22527 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22527step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22527step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22527step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical176
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22528 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22528step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22528step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22528step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22529 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22529step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22529step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22529step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22529step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22530 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22530step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22530step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, -1, 2], ![-1, -1, 2]]
def raw22530step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22530step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw22530step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22530step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw22530step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22531 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22531step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22531step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22531step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 0, 2], ![1, -3, 2]]
def raw22531step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22531step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw22531step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22531step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw22531step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22532 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22532step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22532step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22532step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22532step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22533 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22533step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22533step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22533step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22533step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22533step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22533step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22534 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22534step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22534step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22534step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22534step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22535 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22535step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22535step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22535step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 1, 2], ![1, -3, 2]]
def raw22535step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22535step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw22535step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22535step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw22535step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22536 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22536step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22536step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22536step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22537 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22537step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22537step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22537step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22538 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22538step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22538step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22538step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22539 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22539step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22539step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22539step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22539step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-3, 1, 2], ![0, -2, 2]]
def raw22539step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22539step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw22539step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22540 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22540step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22540step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22540step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 0, 2], ![-1, -1, 2]]
def raw22540step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22540step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def raw22540step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22541 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22541step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22541step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22541step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22541step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22542 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22542Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22542step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22543 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22543Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22543step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22544 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22544Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22544step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22544step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22544step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22544step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22545 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22545Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22545step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22545step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22546 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22546Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22546step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22546step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22547 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22547Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22547step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22548 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22548Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22548step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22549 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22549Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22549step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22549step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22549step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22550 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22550Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22550step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22550step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22550step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22551 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22551step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22551step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22551step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22552 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22552step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22553 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22553Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22553step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22554 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22554Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22554step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22554step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22554step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22555 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22555Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22555step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22555step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22555step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22556 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22556Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22556step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22556step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22556step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, -1, 2], ![0, -2, 2]]
def raw22556step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22556step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22556step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22557 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22557Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22557step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22557step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22558 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22558Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22558step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22558step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22558step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22559 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22559Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22559step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22559step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22559step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22560 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22560Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22560step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22560step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22560step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, -1, 2], ![-1, -1, 2]]
def raw22560step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22560step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw22560step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22561 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22561step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22561step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22561step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 0, 2], ![1, -3, 2]]
def raw22561step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22561step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw22561step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22562 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22562Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22562step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22562step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22563 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22563Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22563step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22563step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22563step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22564 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22564step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22564step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22564step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22565 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22565step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22565step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22565step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 1, 2], ![1, -3, 2]]
def raw22565step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22565step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw22565step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22566 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22566step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, -1, 2], ![0, -2, 2]]
def raw22566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22566step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw22566step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22566step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw22566step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22567 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22567step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22567step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22568 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22568step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22568step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22568step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22568step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22569step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22569step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22569step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22570step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22570step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22571step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22571step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22572step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22573step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22573step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22573step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22574step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22575step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22575step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22576step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22576step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22576step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22577step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22577step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22577step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22577step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22578step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22578step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22579step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22579step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22579step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22579step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22580step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22581step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![3, -2, -1], ![2, -1, -1]]
def raw22581step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22581step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw22581step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22581step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw22581step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22582step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22582step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22582step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22582step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22583step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22583step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22583step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22584step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22584step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22584step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw22585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw22585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw22585step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22585step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![3, -2, -1], ![1, 0, -1]]
def raw22585step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22585step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw22585step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22585step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw22585step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22586step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22587step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22587step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22588step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22588step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22589step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22589step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22589step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -1, -1], ![1, 0, -1]]
def raw22589step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22589step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw22589step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22590step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22591step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22591step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22592step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22592step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22593step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22593step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22593step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22593step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22594step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22594step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22594step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22594step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22595step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22595step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22596step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22597step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22597step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22597step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22598step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22598step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22599step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22599step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22600step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22601step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22601step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22601step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22602step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22602step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22602step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![3, -2, -1], ![2, -1, -1]]
def raw22602step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22602step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw22602step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22603Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22603step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22603step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22604Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22604step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22604step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22605Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22605step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22605step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22605step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw22606Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw22606step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw22606step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22606step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![3, -2, -1], ![1, 0, -1]]
def raw22606step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22606step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw22606step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22607 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22607step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22607step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22607step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22608 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22608step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22608step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22608step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22609 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22609step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22609step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22609step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22609step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22609step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22609step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22610 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22610step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw22610step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22610step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22610step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22610step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22610step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22611 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22611step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22611step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22611step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22611step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22612 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22612step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22612step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22613 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22613step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22613step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22614 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22614step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22614step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22614step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22614step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22614step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22615 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22615step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22615step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22615step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22615step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22615step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22616 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22616step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22616step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22617 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22617step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22617step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22618 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22618step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22618step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22618step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22618step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22619 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22619step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22619step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22619step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22619step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22619step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22620 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22620step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22620step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22621 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22621step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22622 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22622step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22622step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22622step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22622step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22623 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22623step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22623step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-1, -1, 2]]
def raw22623step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22623step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22623step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22623step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22623step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22624 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22624step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22624step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22624step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22624step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22624step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22625 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22625step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22625step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22625step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22625step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22625step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22626 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22626step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22626step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22626step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22626step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22626step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22627 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22627step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22627step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -2, 2], ![-2, 0, 2]]
def raw22627step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22627step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw22627step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22627step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw22627step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22628 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22628step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22628step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 0, 2], ![0, -2, 2]]
def raw22628step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22628step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw22628step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22628step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw22628step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22629 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22629step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22629step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22629step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22629step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22630 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22630step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22630step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22630step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22631 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22631step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22631step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22631step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22632 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22632step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22632step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw22632step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22632step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def raw22632step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22633 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22633step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22634 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22635 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22635step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22636 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22636step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22637 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22637step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22638 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22639 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22640 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22640step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22641 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22641step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22641step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22642 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22643 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22644 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22644step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22644step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22644step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22645 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22645step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22645step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-1, -1, 2]]
def raw22645step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22645step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22645step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22646 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22646step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22647 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22647step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22648 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22648step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22649 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22649step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22649step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -2, 2], ![-2, 0, 2]]
def raw22649step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22649step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw22649step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22650 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22650step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22650step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 0, 2], ![0, -2, 2]]
def raw22650step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22650step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw22650step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22651 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22651step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22651step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22652 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22652step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22652step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22653 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22653step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 0, 2], ![-1, -1, 2]]
def raw22653step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22653step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw22653step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22653step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw22653step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22654 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22654step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22654step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw22654step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22654step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw22654step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical177
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22656step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22656step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22657step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22657step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22660step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22661step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22661step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22661step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22664step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22664step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22664step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22665step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22666step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22666step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22668step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22668step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22668step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22668step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22669step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22670step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22671step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end


