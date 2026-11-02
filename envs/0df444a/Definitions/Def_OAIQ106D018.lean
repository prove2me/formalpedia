-- Prove2me | Definitions.Def_OAIQ106D018
-- name    : OAIQ106D018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:06:10.526383+00:00
-- url     : https://prove2.me/theorems/9945507b-c07e-4b08-ba1d-afc798e506be
-- title:
--   Definitions bundle OAIQ106D018 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7409 declarations of OpenAI's Lean: 7409 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw20538step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20538step2`, `OAI.MUB6.Certificate.MixedSemantics.raw20538step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20539`, `OAI.MUB6.Certificate.MixedSemantics.raw20539Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20539step0`, `OAI.MUB6.Certificate.MixedSemantics.raw20539step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20539step1`, `OAI.MUB6.Certificate.MixedSemantics.raw20539step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20539step2`, `OAI.MUB6.Certificate.MixedSemantics.raw20539step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2053Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2053step0`, `OAI.MUB6.Certificate.MixedSemantics.raw2053step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2054`, `OAI.MUB6.Certificate.MixedSemantics.raw20540`, `OAI.MUB6.Certificate.MixedSemantics.raw20540Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20540step0`, `OAI.MUB6.Certificate.MixedSemantics.raw20540step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20540step1`, `OAI.MUB6.Certificate.MixedSemantics.raw20540step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20540step2`, `OAI.MUB6.Certificate.MixedSemantics.raw20540step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20540step3`, `OAI.MUB6.Certificate.MixedSemantics.raw20540step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20541`, `OAI.MUB6.Certificate.MixedSemantics.raw20541Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20541step0`, `OAI.MUB6.Certificate.MixedSemantics.raw20541step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20541step1`, `OAI.MUB6.Certificate.MixedSemantics.raw20541step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20541step2`, `OAI.MUB6.Certificate.MixedSemantics.raw20541step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20542`, `OAI.MUB6.Certificate.MixedSemantics.raw20542Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20542step0`, `OAI.MUB6.Certificate.MixedSemantics.raw20542step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20542step1`, `OAI.MUB6.Certificate.MixedSemantics.raw20542step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20542step2` and 7369 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical1`, `MutuallyUnbiased_MixedSemantics_Canonical16`, `MutuallyUnbiased_MixedSemantics_Canonical160`, `MutuallyUnbiased_MixedSemantics_Canonical161`, `MutuallyUnbiased_MixedSemantics_Canonical162`, `MutuallyUnbiased_MixedSemantics_Canonical163`, `MutuallyUnbiased_MixedSemantics_Canonical164`, `MutuallyUnbiased_MixedSemantics_Canonical165`, `MutuallyUnbiased_MixedSemantics_Canonical166`, `MutuallyUnbiased_MixedSemantics_Canonical167`, `MutuallyUnbiased_MixedSemantics_Canonical168`, `MutuallyUnbiased_MixedSemantics_Singletons41`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1162`, `OAI.MUB6.Certificate.MixedSemantics.sound2527`, `OAI.MUB6.Certificate.MixedSemantics.sound2530`, `OAI.MUB6.Certificate.MixedSemantics.sound2531`, `OAI.MUB6.Certificate.MixedSemantics.sound2532`, `OAI.MUB6.Certificate.MixedSemantics.sound2636`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound106`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound107`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound22`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound69`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound71`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound72`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound73`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound74`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound75`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound90`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1780`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero733`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero863`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1123`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1158`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1169`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound129`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1483`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1490`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1674`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1848`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2045`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound446`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound503`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound536`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound721`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound814`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound843`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound901`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound969`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978`.
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

def raw20Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]

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

def raw205Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw205step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw205step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw205step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw206 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw206step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw206step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw207 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw207Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw207step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw207step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw208 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw208step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw208step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw208step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw209 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw209Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw209step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw210 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw210step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw211 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw211Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw211step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw211step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw211step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw212 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw212step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw213 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw213Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw213step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw214 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw214step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw215 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw215Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw215step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw215step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw216 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]

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

def raw2053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw2053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2054 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw2054Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw2054step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw2054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2055 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2055step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2056 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2057 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2057Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw2057step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2057step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2057step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2057step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw2058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw2058step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw2058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2059 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw2059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw2059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw2060Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw2060step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw2060step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2060step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw2060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2061 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2061step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2061step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2061step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2062 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2063Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw2063step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw2063step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2063step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw2063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2064step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2065 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2066 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2066Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2066step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2066step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2066step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw2073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw2073step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw2073step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2074 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw2074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw2074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2075 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw2075Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2075step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2076 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2076step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2077 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2078 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2078Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw2078step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2078step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw2079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2079step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2080 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw2080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2081 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw2081Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2081step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2082 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2082step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2082step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2083 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2084 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2084Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw2084step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2084step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2085 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2085step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2086 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2086step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2087 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2087Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2087step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2087step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2087step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2088 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2088step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2089 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2090 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2090Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw2090step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2090step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2091 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2091step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2092 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2093 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2093Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw2093step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2093step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2093step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2094 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2094step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2094step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2095 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2096 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2096Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw2096step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2096step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2096step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2097 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw2097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw2097step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw2097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2098 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw2098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw2098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2099 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw2099Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw2099step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw2099step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw2099step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2100step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2101 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2102 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2102Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw2102step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2102step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2102step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2102step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2103 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw2103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw2103step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw2103step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2104 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw2104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw2104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2105 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw2105Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw2105step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw2105step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw2105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2106 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2106step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2106step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2107 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2108 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2108Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw2108step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw2108step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw2108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2109 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2109step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2110 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2110step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2111 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2111Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw2111step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw2111step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw2111step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2112 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2112step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2112step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2114 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2114Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2114step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2114step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2114step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2115 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw2115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw2115step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw2115step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2116 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw2116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw2116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2117 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw2117Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw2117step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw2117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2118 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw2118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2118step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2118step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2119 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw2119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2120 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw2120Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw2120step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2120step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2121 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2121step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2121step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2121step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2122 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2123 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2123Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2123step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2123step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2123step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2123step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2124 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw2124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw2124step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw2124step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2125 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw2125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw2125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2126 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw2126Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw2126step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw2126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2127 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2127step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2127step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2128 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2129 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2129Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2129step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2129step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2129step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2130 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2130step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2130step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2131 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2131step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2132 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2132Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw2132step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw2132step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw2132step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2133 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![-2, 3, -1]]
def raw2133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2133step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw2133step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw2133step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2134 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![-2, 3, -1]]
def raw2134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2134step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw2134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2135 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![-2, 3, -1]]
def raw2135Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2135step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw2135step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2135step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw2135step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2135step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw2135step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2136 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 2, 0], ![1, 2, -3]]
def raw2136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2136step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw2136step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw2136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2137 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 2, 0], ![1, 2, -3]]
def raw2137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2137step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw2137step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2138 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 2, 0], ![1, 2, -3]]
def raw2138Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2138step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw2138step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2138step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw2138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2139 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw2139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2139step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2140 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw2140Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2141 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw2141Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw2141step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw2141step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2141step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw2141step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2142 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw2142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw2142step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2142step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw2142step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2143 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw2143Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2143step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2144 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw2144Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw2144step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw2144step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2144step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw2144step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2154 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2154step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2155 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2155Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2155step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2156 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2156Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw2156step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2156step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2156step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2156step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2157 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw2157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw2157step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw2157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2158 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw2158Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw2158step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2159 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw2159Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw2159step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2159step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2159step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2160 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2160step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2160step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2160step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2161 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2161Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2162 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20538step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20538step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20538step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20539step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20539step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20539step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20540step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20540step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20540step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20540step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20540step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20540step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20541step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20541step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20542step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20542step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20543step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20543step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def raw20543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20543step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw20543step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20543step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw20543step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20544step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20544step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20544step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20544step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20545step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20545step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20545step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20545step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20545step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20546step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20546step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20546step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20546step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20546step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20547step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 1, -2], ![4, -4, 0]]
def raw20547step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20547step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw20547step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20547step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw20547step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20548step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20548step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20548step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20548step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20548step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20548step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20549step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20549step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20549step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20549step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20549step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20550step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20550step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20550step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20550step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20550step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20551step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20551step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20551step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20552step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20553Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20553step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20554Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20554step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20554step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20554step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20555Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20555step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20556Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20556step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20557Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20557step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20557step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20558Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20558step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20559Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20559step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20560Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20560step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20560step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20560step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def raw20560step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20560step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw20560step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20561step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20561step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20562Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20562step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20562step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20563Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20563step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20563step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20563step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20564step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20564step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20564step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 1, -2], ![4, -4, 0]]
def raw20564step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20564step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw20564step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20565step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20565step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20565step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20565step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20565step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20566Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20566step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20566step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20566step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20566step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20567Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20567step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20567step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20567step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20567step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20590 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20590step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20591 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20591step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20591step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20591step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20591step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20592 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20592step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20592step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20593 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20593step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20593step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20593step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-3, 2, 1], ![0, -3, 3]]
def raw20593step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20593step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def raw20593step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20594 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20594step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20594step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20594step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, -2, 3]]
def raw20594step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20594step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw20594step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20595 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20595step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20595step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20595step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20596 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20596step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20597 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20597step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20598 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20598step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20598step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw20598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20599 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20599step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20599step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20599step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20599step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw20599step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20600 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20600step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20600step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20600step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20600step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20601 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20601step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20602 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20602step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20603 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20603Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20603step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20603step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw20603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20604 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20604Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20604step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20604step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw20604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20605 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20605Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20605step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20605step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20605step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20606 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20606Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20606step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20607 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20607Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20607step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20607step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20608 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20608Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20608step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20608step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw20608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20609 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20609Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20609step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20609step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20609step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20609step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw20609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20610 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20610Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20610step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20610step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20610step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -3, 3]]
def raw20610step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20610step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw20610step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20611 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20611Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20611step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20611step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20611step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20612 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20612Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20612step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20612step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20612step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20613 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20613Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20613step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20613step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20614 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20614step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20614step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20614step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, -2, 3]]
def raw20614step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20614step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20614step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20615 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20615Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20615step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20615step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20615step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![1, -4, 3]]
def raw20615step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20615step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw20615step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20616 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20616Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20616step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20616step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw20616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20617 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20617Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20617step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20617step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw20617step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20618 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20618Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20618step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20618step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw20618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20619 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20619Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20619step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20619step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20619step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 2, 1], ![1, -4, 3]]
def raw20619step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20619step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![3, 1, -4]]
def raw20619step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20620 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20620step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20620step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20620step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20620step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20620step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20621 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20621step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20621step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20621step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20621step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20621step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20622 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20622step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20622step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20622step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20622step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20622step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20623 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20623step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20623step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20623step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-3, 2, 1], ![0, -3, 3]]
def raw20623step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20623step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw20623step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20623step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw20623step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20624 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20624step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20624step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20624step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20624step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20624step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20624step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20625 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20625step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20626 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20627 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20627step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20627step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20627step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20627step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20627step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20628 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20628step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20628step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20628step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20628step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20628step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20629 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20629step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20629step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20629step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20630 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20630step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20631 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20631step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20631step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20631step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20631step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20631step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20631step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20632 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20632step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20632step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20632step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20632step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20632step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20633 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20633step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20633step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20634 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20634step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20634step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20635 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20635step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20635step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20635step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20635step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20635step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20636 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20636step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20636step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20636step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, -2, 3]]
def raw20636step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20636step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw20636step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20636step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw20636step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20637 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20637Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20637step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20637step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20637step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![1, -4, 3]]
def raw20637step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20637step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 1, -2], ![3, -4, 1]]
def raw20637step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20637step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 1, -2], ![3, -4, 1]]
def raw20637step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20638 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20638Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20638step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20638step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20638step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20638step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20638step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20638step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20639 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20639Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20639step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20639step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20639step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20639step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20639step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20639step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20640 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20640step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20640step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20640step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20640step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20640step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20641 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20641Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20641step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20641step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20641step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 2, 1], ![1, -4, 3]]
def raw20641step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20641step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 2, -3], ![3, -4, 1]]
def raw20641step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20641step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 2, -3], ![3, -4, 1]]
def raw20641step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20642 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20642step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -3, 3]]
def raw20642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20642step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw20642step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20643 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20643step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20643step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20643step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20644 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20644step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20644step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20644step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20645 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20645step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20645step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20645step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20645step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20646 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20646step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![1, -4, 3]]
def raw20646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20646step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw20646step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20647step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw20647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20647step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw20647step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw20648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20648step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw20648step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw20649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20649step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw20649step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw20650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw20650step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw20650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20650step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw20650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20651step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20651step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20652step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20655step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20656step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20659step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20659step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20659step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20660step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20661step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20661step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20662step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20662step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20662step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20663step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20663step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20663step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20664step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20665step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20667step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20667step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20667step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20668step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20670step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20672step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20673Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20673step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20673step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20674Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20674step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20674step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20674step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw20674step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20675Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20675step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20675step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw20675step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20676Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20676step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20676step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20676step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw20676step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20677Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20677step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20677step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20678step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20679step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20680step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20681step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw20681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20684step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20685step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20685step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw20686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20687step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20687step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20689step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20690step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20690step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20691step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20691step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw20691step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20692step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20693step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20695step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20696step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20696step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw20696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20697step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20697step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20700step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20700step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20700step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw20700step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20701step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20701step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20701step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20702step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20702step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20703step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20704step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20704step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 1, -3]]
def raw20704step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20704step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 1, -3]]
def raw20704step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20705step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20705step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20705step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20705step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20705step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20706step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw20706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20706step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw20706step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20706step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw20706step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20707step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20708step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20708step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20708step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20709step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw20709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw20709step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20709step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw20709step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20711step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw20711step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20711step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20711step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20711step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20712step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20712step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20713step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20713step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20714step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw20714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw20714step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20714step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw20714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20715step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20715step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20715step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw20716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20716step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20716step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20716step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20717step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20717step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20717step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw20717step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20717step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20717step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20717step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20717step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw20718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20718step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw20719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20719step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20719step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20719step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20720step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20720step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20720step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20720step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20720step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20720step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20721step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20721step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20721step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20721step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw20721step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20721step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20721step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20721step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20721step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20722step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20722step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20722step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw20722step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20722step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20722step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20722step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20722step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw20723step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20723step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20723step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw20724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20724step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20724step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20725step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw20725step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20725step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw20725step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20725step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw20725step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20726step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20726step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw20726step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw20726step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20726step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw20726step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20727step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw20727step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20727step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20727step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20727step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20727step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw20728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20728step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20728step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw20729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20729step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20729step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20730step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20730step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20730step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20731step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20731step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20731step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20731step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20732step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20733step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20738 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]
def raw20738Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20738step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]
def raw20738step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20738step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw20738step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw20739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20746Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20746step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20749step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20749step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20749step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20750step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20750step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20751step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20751step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20752step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20752step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20752step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20753step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20753step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20754step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20754step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20755step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20755step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20755step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20756step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20756step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20756step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20756step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20756step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20757step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20757step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20757step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20758step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20758step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20759step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20759step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20760step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20760step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20760step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw20760step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20760step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20760step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20760step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20760step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20761step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20761step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20761step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20762step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20762step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20763step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20763step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20763step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20764step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20764step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20764step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw20764step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20764step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw20764step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw20765step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20765step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw20765step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20766step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20766step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20766step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20766step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20767step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20767step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20767step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20768step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20768step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20768step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw20768step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20768step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw20768step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20768step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw20768step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![4, -3, -1]]
def raw20769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw20769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw20769step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20769step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw20769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20769step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw20769step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20769step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw20769step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20769step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw20769step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20770step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20771Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20772Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20772step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20772step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20773Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20773step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20773step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20773step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20773step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20774Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20774step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20774step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20776step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20776step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20777step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20777step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20777step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20777step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20778step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20778step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20778step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20778step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20778step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20779step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20781step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20781step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw20781step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20781step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20781step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20782step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20782step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20782step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20782step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20785step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20785step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw20785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20786step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw20786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20787step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20789step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20789step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw20789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20789step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw20789step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![4, -3, -1]]
def raw20790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw20790step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw20790step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20790step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw20790step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20790step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw20790step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20790step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw20790step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20795 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20795step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20795step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20798 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20798step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20798step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20803 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20803step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw20803step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20803step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw20803step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20817 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20817Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20817step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20821 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20821Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20821step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20821step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20827 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20827step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20827step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20827step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, -2, 3]]
def raw20827step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20827step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw20827step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20830 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20830step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20830step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20830step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, -1, 3]]
def raw20830step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20830step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw20830step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20840 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20841 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20842 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20842step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20842step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw20842step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20843step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20843step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20843step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20843step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20844step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20845step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20846step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20848step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20848step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20848step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20849step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20849step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20849step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20849step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20850step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20850step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20852step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20852step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20852step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20853step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20853step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20853step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20853step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20854step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20854step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20854step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20855step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20855step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20855step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20855step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20856step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20856step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20856step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw20856step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20857step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20857step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20857step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20857step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20858step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20858step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20859step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20859step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20860step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20861step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20861step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20861step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20861step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20862step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20864step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw20864step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20864step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw20864step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw20865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20865step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20865step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw20865step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20865step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw20865step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20865step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw20865step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20866step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20866step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20866step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw20866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20867step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20869step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20870step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20870step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20871step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20873step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20874step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20874step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20874step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20874step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20875step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20875step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20875step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20876step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20877step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20878step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20878step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20878step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw20878step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20878step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw20878step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20879step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20879step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20879step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20880step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20881step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20882step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20882step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20883step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20883step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20883step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20883step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20884step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20885step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20886Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20886step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20886step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20886step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw20886step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw20887Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20887step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20887step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20887step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw20887step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20887step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw20887step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20888Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20888step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20888step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20888step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20888step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20888step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20888step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20889Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20889step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw20889step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw20889step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20889step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw20889step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20890Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20890step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20891Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20891step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20891step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20891step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20892Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20892step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20892step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20892step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20892step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20892step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20893Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20893step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw20893step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw20893step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20893step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw20893step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20894Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20894step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20895Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20895step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20895step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20895step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20895step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20896Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20896step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20896step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20896step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20896step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20896step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20897Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20897step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20897step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw20897step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20897step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20897step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20897step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20897step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20898Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20898step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20899Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20899step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20899step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20900Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20900step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20900step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20900step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw20900step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20900step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw20900step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20900step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw20900step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20901Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20901step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20901step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw20901step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20901step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw20901step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20901step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw20901step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20902Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20902step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20902step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20903Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20903step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20903step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20903step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20903step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20904Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20904step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20904step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20904step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw20904step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20904step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw20904step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20905Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20905step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20905step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20905step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw20905step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20905step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw20905step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20905step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw20905step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20906Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20906step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20906step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20906step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20906step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20907Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20907step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20907step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20908Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20908step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20908step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20908step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20908step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20908step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20908step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw20909Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20909step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20909step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20909step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw20909step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20909step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw20909step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20909step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw20909step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20916 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-1, 1], ![0, 0], ![3, -3]]
def raw20916Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20916step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-1, 1], ![3, -3]]
def raw20916step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20916step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![3, -3]]
def raw20916step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20916step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw20916step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20916step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw20916step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20916step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw20916step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20919step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20919step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw20921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20921step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20921step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20925step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20925step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20926step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw20926step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20926step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20926step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20927step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20928step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20929step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20929step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw20929step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20929step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw20929step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20930step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20930step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20930step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20931step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20931step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20931step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20932step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20932step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20933step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20933step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20933step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20934step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20934step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20934step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20935step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20935step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20935step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20936step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20936step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20936step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20937step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20937step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20938step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20938step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20939step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20939step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20939step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20940step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20940step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20941step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20941step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw20942step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw20942step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw20943step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20943step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw20943step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20944step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20944step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20944step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20944step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20945step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20945step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20945step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20945step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20946step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20946step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-4, 2, 2]]
def raw20946step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20946step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw20946step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20946step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw20946step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20947step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20947step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20948step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20949step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20951step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20952step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20953step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20953step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20953step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20953step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20954step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20954step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20955step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20955step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20956step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20956step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20956step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20959step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20959step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw20959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20960step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw20960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20962step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20963step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-4, 2, 2]]
def raw20963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20963step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw20963step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20980 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20980step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20994 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20994step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20995 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20995step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20996 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20997 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw20997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw20998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw20998step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw20998step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20998step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw20999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw20999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw20999step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 1, -4]]
def raw21000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 1, -4]]
def raw21000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![3, 1, -4]]
def raw21000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21000step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21000step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21000step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw21001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw21001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw21001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw21003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw21004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw21006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw21006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21006step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw21006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21008 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-2, 2], ![2, -2], ![2, -2]]
def raw21008Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21008step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![2, -2], ![2, -2]]
def raw21008step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21008step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw21008step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw21009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw21010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw21012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw21012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw21012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw21014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21014step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw21015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21016step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw21016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21016step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw21017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw21017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw21017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw21017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21017step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21017step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21019 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-2, 2], ![1, -1], ![3, -3]]
def raw21019Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21019step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![1, -1], ![3, -3]]
def raw21019step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21019step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]
def raw21019step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21019step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw21019step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21019step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw21019step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw21022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw21022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw21022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![4, -1, -3]]
def raw21023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![4, -1, -3]]
def raw21023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21023step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![4, -1, -3]]
def raw21023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21023step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw21023step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21023step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21023step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw21024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw21025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw21027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw21027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw21027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw21034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21034step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw21035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21035step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21036step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw21036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21036step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21036step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![3, 1, -4]]
def raw21037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 1, -4]]
def raw21037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![3, 1, -4]]
def raw21037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21037step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![3, 1, -4]]
def raw21037step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21037step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw21037step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21037step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw21037step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw21038Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw21038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw21038step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21039 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-2, 2], ![0, 0], ![4, -4]]
def raw21039Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21039step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-2, 2], ![4, -4]]
def raw21039step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21039step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![4, -4]]
def raw21039step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21039step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![4, -4]]
def raw21039step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21039step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-2, 2], ![-2, 2]]
def raw21039step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21039step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw21039step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw21041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21041step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21041step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21042step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21043step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw21044step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21044step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21046 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw21046Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21046step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw21046step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21046step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw21046step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21046step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw21046step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw21047step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw21050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw21050step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21051step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw21052step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21053step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21054step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw21055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21055step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21057 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw21057Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21057step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw21057step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21057step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw21057step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21057step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw21057step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21061step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw21061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21061step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw21062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21063step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw21071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw21071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw21072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw21072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21072step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw21073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw21073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21073step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21073step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 1, -4]]
def raw21074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 1, -4]]
def raw21074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, 1, -4]]
def raw21075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw21075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw21075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21075step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw21075step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21075step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21075step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw21076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw21076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21077 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![4, -4]]
def raw21077Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21077step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![-1, 1], ![4, -4]]
def raw21077step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21077step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![4, -4]]
def raw21077step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21077step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw21077step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21077step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw21077step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21078step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw21078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![3, -1, -2]]
def raw21079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw21080step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw21081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21082step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21082step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![3, -1, -2]]
def raw21082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21082step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw21083step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21084 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![-1, 1], ![2, -2]]
def raw21084Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21084step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![-1, 1], ![2, -2]]
def raw21084step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21084step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![2, -2]]
def raw21084step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21084step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw21084step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21085Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21085step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw21085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21085step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21086step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21087step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw21088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw21088step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw21088step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21090step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21091step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw21093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw21093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw21093step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw21094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21095 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![-1, 1], ![1, -1], ![1, -1]]
def raw21095Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21095step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![1, -1], ![1, -1]]
def raw21095step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21095step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw21095step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw21099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw21099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw21099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21102step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21103Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21103step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw21104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![3, -1, -2]]
def raw21104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw21105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21106 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![-1, 1], ![0, 0], ![2, -2]]
def raw21106Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21106step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![-1, 1], ![2, -2]]
def raw21106step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21106step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![2, -2]]
def raw21106step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21106step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw21106step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw21107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21109Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21109step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw21110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw21110step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw21110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21112Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21112step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw21115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw21116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21117 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![-1, 1], ![2, -2]]
def raw21117Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21117step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![-1, 1], ![2, -2]]
def raw21117step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21117step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw21117step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21118Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw21118step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw21119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical165
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw21120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21120Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21120step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw21121Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw21121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw21126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw21126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21128 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw21128Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21128step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw21128step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21130Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21130step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw21132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw21132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21133Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21133step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21135Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21135step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21136Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21136step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw21137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw21137step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21137step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21138step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21139 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![-1, 1], ![0, 0], ![2, -2]]
def raw21139Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21139step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![-1, 1], ![2, -2]]
def raw21139step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21139step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw21139step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21140Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21141Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21141step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21142Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw21143Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw21143step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21144step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21144step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21145step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21145step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21147step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw21148step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21148step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21148step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21156step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21158step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21160step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21161step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21162step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21162step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21162step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, -1, 2], ![-4, 3, 1]]
def raw21162step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21162step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21162step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21162step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21162step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21163step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21164step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw21165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw21165step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw21165step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21166step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21166step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21166step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, -1, 2], ![-3, 3, 0]]
def raw21166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21166step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw21166step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw21167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw21168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw21169step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21169step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw21169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21169step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw21169step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21170step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw21170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21171step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21171step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21174step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw21174step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21174step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21175step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21175step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw21175step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21176step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21178step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21179step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21182step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21183step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21184step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21186Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21186step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21186step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw21186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21187Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21187step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21187step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw21187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21188Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21188step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw21188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21189Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21189step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw21189step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw21190Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw21190step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21190step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw21190step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21190step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw21190step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21191Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21191step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21191step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21191step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21191step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw21191step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21192Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21192step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21192step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21192step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21192step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, -1, 2], ![-4, 3, 1]]
def raw21192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21192step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21192step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21193Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21193step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw21193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21193step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21194Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21194step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw21194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw21195Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw21195step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw21195step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21195step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-4, 3, 1]]
def raw21195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21195step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw21195step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21196step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21196step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21196step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw21196step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21196step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw21196step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21196step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw21196step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21197step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21197step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21197step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21197step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw21197step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21197step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw21197step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21197step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw21197step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21198step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw21198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw21198step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21198step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw21198step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21199step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw21199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw21199step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21199step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw21199step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21200step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw21200step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21200step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21200step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21200step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21200step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21200step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21200step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21201step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21201step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21201step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21201step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21201step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21202step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw21202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw21202step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw21202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21203step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21203step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21203step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21203step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21203step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw21204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw21204step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21204step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw21204step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21205step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21205step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21205step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21205step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21205step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21206step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw21206step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw21206step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21206step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw21206step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21207step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21207step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21207step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21207step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21208step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw21208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw21208step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw21208step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21209step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21209step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21209step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21209step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw21209step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21209step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw21209step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21209step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw21209step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21210step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21210step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21210step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw21210step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21210step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw21210step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21210step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw21210step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21211step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw21211step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw21211step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21211step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw21211step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21212step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw21212step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21212step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw21212step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21212step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw21212step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21213Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21213step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21213step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw21213step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw21213step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21213step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw21213step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21214step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21214step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21214step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw21214step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21214step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw21214step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21215Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21215step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw21215step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw21215step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21216Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21216step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw21216step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw21216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw21217Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw21217step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw21217step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21217step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw21217step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21217step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw21217step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21218step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21219step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21220step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21222step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21223step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21223step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21224Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21224step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21224step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21225step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw21226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21226step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21227step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21227step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21231Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21231step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21231step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21232Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21232step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21233step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21234Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21234step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21234step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21235Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21235step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21235step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21236step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21236step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21236step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21237step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21238step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw21238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21238step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![3, -1, -2]]
def raw21238step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21238step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw21238step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21238step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw21238step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21239step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21239step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21239step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21239step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21240step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21240step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21240step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21241step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21241step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21241step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![3, -1, -2]]
def raw21242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21242step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw21242step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21242step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw21242step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21242step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw21242step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21243step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw21243step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21243step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw21243step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21244step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21244step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21244step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21245step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21245step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21246step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21247step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21247step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21247step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21247step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw21248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw21248step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw21248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21249step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21249step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21250step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21251step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21251step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21251step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21252step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21252step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21252step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21252step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21252step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21252step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21253step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -2, 0], ![3, -1, -2]]
def raw21253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21253step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21253step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21253step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21253step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21254step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![3, -1, -2]]
def raw21254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21254step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21254step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21254step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21254step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21255step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21256step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21256step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw21257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw21257step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21257step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw21257step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21257step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw21257step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21257step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw21257step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![4, -2, -2]]
def raw21258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21258step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21258step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21258step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21258step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![4, -2, -2]]
def raw21259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21259step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21259step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21259step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21259step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21260step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21260step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21261step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![4, -2, -2]]
def raw21262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21262step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![4, -2, -2]]
def raw21262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21262step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21262step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21262step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21262step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21263step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21263step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21271step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21271step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21271step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw21271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21276step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw21276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21278step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21281Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21281step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -2, 0], ![3, -1, -2]]
def raw21281step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21281step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21282Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21282step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![3, -1, -2]]
def raw21282step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21283Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21283step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21283step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21284Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21284step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21284step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21291 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21291step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21291step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21292 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21292step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21292step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21292step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21292step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21292step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21293 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21293step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21293step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21293step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21293step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21293step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21294 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21294step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21294step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21295 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21295step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21295step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21296 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21296step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21296step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw21296step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21296step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw21296step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21297 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw21297step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21297step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw21297step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21298 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21298step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21298step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21299 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21299step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21299step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21299step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21299step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21300 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21300step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21301 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21301step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21301step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21302 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21302step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21302step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21303 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21303step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21303step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21304 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21304step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21304step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21304step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21304step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21305 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21305step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21305step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21306 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21306step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21306step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21307 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21307step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21307step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21307step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21307step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21308 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21308step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21308step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21308step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21308step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21309 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21309step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, -1, 3]]
def raw21309step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21309step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw21309step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21309step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw21309step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21310 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21310step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21310step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21311 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21311step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21311step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21312 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21312step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21312step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw21312step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21312step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw21312step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21313 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21313step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21313step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21313step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21313step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21314 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21314step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21314step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21315 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21315Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21315step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21316 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21316Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21316step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21316step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21316step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21316step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21317 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21317Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21317step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21317step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21317step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21317step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21317step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21318 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21318Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21318step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21318step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21318step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21319 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21319Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21319step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21320 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21320Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21320step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21321 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21321Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21321step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21321step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21321step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21321step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw21321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21322 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21322Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21322step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21322step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw21322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21323 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21323Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21323step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21324 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21324Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21324step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21324step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21324step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21324step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21325 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21325Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21326 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21326Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21326step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21327 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21327Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21327step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21328 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21328Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21328step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21329 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21329Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21329step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21329step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21329step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21330 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21330Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21331 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21331Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21331step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21332 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21332Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21332step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21333 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21333Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21333step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21333step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21334 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21334step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21334step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21334step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, -1, 3]]
def raw21334step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21334step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw21334step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21335 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21335step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21336 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21336step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21336step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21337 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21337step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw21337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21338 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21338step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21338step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21338step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21339 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21339step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21340 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21340step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21340step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21340step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21347 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21347Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21347step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21347step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21347step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw21347step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21347step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw21347step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21352 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21352Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21352step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21352step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21357 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21357Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21357step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21357step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21364 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21364Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21364step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21364step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21364step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21364step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw21364step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21364step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw21364step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21365 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21365Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21365step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21365step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21366 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21366Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21366step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21366step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21366step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21367 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21367step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21367step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21367step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21367step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21368 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21368step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21368step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw21368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21368step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw21368step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21369 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21370 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21370step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21371 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21371step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw21371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21371step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw21371step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21372 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21372step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21372step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21372step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw21372step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21373step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21373step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21374step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21374step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21374step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical167
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw21376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21376step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21376step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21377step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21377step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw21377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21377step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw21377step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21378step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21381step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21381step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21385step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21385step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21386step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21387step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21389step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21390step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21391step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21391step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21392step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21393step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21393step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![4, -2, -2]]
def raw21394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21394step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21394step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21395step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21395step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, -1, 2], ![-3, 3, 0]]
def raw21395step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21395step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw21395step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw21396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21396step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21397step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw21397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21398step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw21398step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21398step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21398step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21398step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-3, 3, 0]]
def raw21398step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21398step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw21398step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21399step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21399step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21399step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21399step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw21399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21400step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21400step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21401step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21402step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21403step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw21403step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21403step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw21403step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21403step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![3, -2, -1]]
def raw21403step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21404step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21404step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw21404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21405step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21405step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21408step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21408step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21408step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21409step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw21409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21410step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21411step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21413step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21413step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21413step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21413step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21414step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw21414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21415step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21415step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw21415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21416step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21416step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw21416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21417step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw21417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21418Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21418step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw21418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw21419Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw21419step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw21419step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw21419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21420Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21420step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21420step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw21420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21421Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21421step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21421step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, -1, 2], ![-4, 3, 1]]
def raw21421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21421step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw21421step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21422Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21422step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw21422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21423Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21423step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw21423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21423step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21424Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21424step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21424step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![4, -2, -2]]
def raw21424step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21424step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21424step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21424step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-4, 3, 1]]
def raw21424step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21424step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw21424step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21425Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21425step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21425step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21425step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw21425step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21425step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw21425step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21425step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw21425step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21426Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21426step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21426step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21426step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21426step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21426step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21427Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21427step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21427step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21427step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21427step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21427step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21428Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21428step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21428step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw21428step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21428step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21428step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21428step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-2, -1, 3]]
def raw21428step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21428step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw21428step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21428step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw21428step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21429Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21429step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21429step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21429step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21429step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw21429step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21429step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21429step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21429step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21429step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21430Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21430step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21430step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21430step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21430step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21430step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21430step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21430step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21430step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21431Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21431step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21431step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21431step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21431step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21431step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21432Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21432step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21432step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21432step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21432step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21432step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21433Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21433step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw21433step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21433step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw21433step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21433step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, -1, 3]]
def raw21433step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21433step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw21433step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21433step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw21433step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21434Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21434step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21434step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21434step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw21434step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21434step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21434step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21434step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21434step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21435Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21435step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21435step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21435step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21435step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21435step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21436Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21436step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw21436step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw21436step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21436step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw21436step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21437Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21437step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21437step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21437step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21437step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21438Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21438step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21438step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21438step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21438step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21438step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21438step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21438step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21438step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21438step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21439Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21439step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw21439step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21439step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21439step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21439step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21440Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21440step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21440step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21440step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21440step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21440step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21441Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21441step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw21441step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw21441step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21441step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw21441step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21442step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21442step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21442step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21443step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21443step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21443step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21443step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21443step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21443step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21443step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21443step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21444step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw21444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21444step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21444step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21444step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21445step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21445step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21445step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21445step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw21445step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21445step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw21445step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21445step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw21445step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21446step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21446step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21446step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw21446step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21446step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw21446step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21446step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw21446step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21447step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw21447step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw21447step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21447step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw21447step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21448step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw21448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw21448step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21448step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw21448step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw21449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw21449step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21449step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw21449step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21449step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw21449step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21449step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw21449step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21449step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw21449step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21450step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21450step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21450step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw21450step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21450step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw21450step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21450step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw21450step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21451Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21451step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21451step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21451step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-2, -2, 4]]
def raw21451step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21451step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw21451step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21451step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw21451step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21452step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw21452step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21452step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw21452step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21452step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw21452step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21453Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21453step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw21453step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw21453step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21453step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw21453step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21454step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![4, -2, -2]]
def raw21454step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21454step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21454step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21454step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw21454step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21454step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw21454step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21454step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw21454step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21461 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]
def raw21461Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21461step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]
def raw21461step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21461step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2]]
def raw21461step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21461step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw21461step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21464step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw21464step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21464step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw21464step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21465step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21465step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21465step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21466step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21468step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21469step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21470step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21470step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21472step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21475step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21478step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21478step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21478step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21478step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21479step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21479step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21479step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21480step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21480step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21480step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21481step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21481step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21481step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21482step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21482step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21482step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21483step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21483step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21483step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21484step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21484step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21485step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21485step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21486step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21486step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21486step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21487step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21487step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21488step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21488step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21489step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21489step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21489step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21490step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21490step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw21490step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21490step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21490step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21490step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21490step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21491step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![3, -2, -1]]
def raw21491step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21491step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21491step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21491step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21491step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21492step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21492step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21492step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21493step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21493step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21493step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21493step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw21494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw21494step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw21494step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21494step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw21494step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21494step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw21494step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21495step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21495step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, 0, -1], ![4, -3, -1]]
def raw21495step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21495step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21495step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21495step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21495step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21496step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21496step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![4, -3, -1]]
def raw21496step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21496step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw21496step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21496step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw21496step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21497Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21497step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21497step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21497step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21498Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21498step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21498step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21498step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21499step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21499step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21499step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21499step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21502step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21502step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21502step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw21504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21504step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21506step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21507step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21508step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21510step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw21511step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21511step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21512step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![3, -2, -1]]
def raw21512step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21512step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21513step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21514step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw21515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw21515step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw21515step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw21515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21516step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, 0, -1], ![4, -3, -1]]
def raw21516step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21516step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21517Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21517step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![4, -3, -1]]
def raw21517step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21517step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw21517step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21518Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21518step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21519Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21519step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21550 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21550Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21550step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21550step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw21550step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21550step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw21550step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21551 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21551Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21551step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21551step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21551step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21552 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21552Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21552step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21552step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21552step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21553 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21553Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21553step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21553step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21553step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw21553step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21553step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw21553step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21554 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21554Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21554step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21554step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21555 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21555Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21555step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21555step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21556 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21556Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21556step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21556step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21556step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21557 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21557Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21557step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21557step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21557step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21558 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21558Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21558step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21559 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21559Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21559step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21559step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21560 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21560Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21560step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21560step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21560step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21560step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21560step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21560step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21561 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21561Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21561step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21561step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![-1, 0, 1], ![-3, 3, 0]]
def raw21561step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21561step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, 0, -1], ![3, -3, 0]]
def raw21561step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21561step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, 0, -1], ![3, -3, 0]]
def raw21561step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21562 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21562Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21562step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21562step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21563step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw21563step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw21564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21565step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw21565step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw21566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw21567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw21567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw21567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21568step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -2, 1], ![3, 0, -3]]
def raw21568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21568step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21569step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21569step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw21571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw21571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw21571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21571step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw21572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw21572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw21572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw21573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw21573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw21573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw21574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw21574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw21574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21575 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw21575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw21575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw21575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21575step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw21575step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21575step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw21575step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21576 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw21576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw21576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw21576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21577 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw21577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw21577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw21577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21578 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21578step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21578step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21578step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21578step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21579 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw21579Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw21579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw21579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw21579step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21579step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21579step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21580Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21580step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw21585Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw21585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21586 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]
def raw21586Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21586step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![2, -2], ![1, -1]]
def raw21586step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21586step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw21586step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw21587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw21587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21587step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw21588Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw21589Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw21589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw21590Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw21590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw21590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21591Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21591step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21592Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21592step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21593Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21594Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21594step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw21595Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw21595step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21595step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21596Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21597 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]
def raw21597Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21597step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw21597step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21597step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw21597step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21602Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21602step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21606Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21606step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21607Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21607step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw21608Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw21608step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw21608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21612 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21612Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21612step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw21612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21613Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21613step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21614step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw21614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw21614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21615Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21616Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21616step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21616step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw21617Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw21617step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![3, 0, -3]]
def raw21617step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21617step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw21618Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw21618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21619 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![-1, 1], ![0, 0], ![3, -3]]
def raw21619Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21619step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![-1, 1], ![3, -3]]
def raw21619step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21619step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw21619step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21619step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw21619step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21622Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21622step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw21624Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw21624step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw21624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21625Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21625step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw21626Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw21626step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw21626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw21627Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw21627step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw21628Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2636 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end


