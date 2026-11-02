-- Prove2me | Definitions.Def_OAIQ106D006
-- name    : OAIQ106D006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T11:58:31.64382+00:00
-- url     : https://prove2.me/theorems/476a632f-c991-4fcf-83a7-a394a10c7df2
-- title:
--   Definitions bundle OAIQ106D006 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7415 declarations of OpenAI's Lean: 7415 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw11352Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11352step0`, `OAI.MUB6.Certificate.MixedSemantics.raw11352step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11353`, `OAI.MUB6.Certificate.MixedSemantics.raw11353Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11353step0`, `OAI.MUB6.Certificate.MixedSemantics.raw11353step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11353step1`, `OAI.MUB6.Certificate.MixedSemantics.raw11353step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11354`, `OAI.MUB6.Certificate.MixedSemantics.raw11354Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11354step0`, `OAI.MUB6.Certificate.MixedSemantics.raw11354step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11354step1`, `OAI.MUB6.Certificate.MixedSemantics.raw11354step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11355`, `OAI.MUB6.Certificate.MixedSemantics.raw11355Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11355step0`, `OAI.MUB6.Certificate.MixedSemantics.raw11355step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11355step1`, `OAI.MUB6.Certificate.MixedSemantics.raw11355step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11356`, `OAI.MUB6.Certificate.MixedSemantics.raw11356Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11356step0`, `OAI.MUB6.Certificate.MixedSemantics.raw11356step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11356step1`, `OAI.MUB6.Certificate.MixedSemantics.raw11356step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11357`, `OAI.MUB6.Certificate.MixedSemantics.raw11357Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11357step0`, `OAI.MUB6.Certificate.MixedSemantics.raw11357step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11358`, `OAI.MUB6.Certificate.MixedSemantics.raw11358Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11358step0`, `OAI.MUB6.Certificate.MixedSemantics.raw11358step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11358step1`, `OAI.MUB6.Certificate.MixedSemantics.raw11358step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11359`, `OAI.MUB6.Certificate.MixedSemantics.raw11359Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw11359step0` and 7375 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical8`, `MutuallyUnbiased_MixedSemantics_Canonical88`, `MutuallyUnbiased_MixedSemantics_Canonical89`, `MutuallyUnbiased_MixedSemantics_Canonical9`, `MutuallyUnbiased_MixedSemantics_Canonical90`, `MutuallyUnbiased_MixedSemantics_Canonical91`, `MutuallyUnbiased_MixedSemantics_Canonical92`, `MutuallyUnbiased_MixedSemantics_Canonical93`, `MutuallyUnbiased_MixedSemantics_Canonical94`, `MutuallyUnbiased_MixedSemantics_Canonical95`, `MutuallyUnbiased_MixedSemantics_Canonical96`, `MutuallyUnbiased_MixedSemantics_Canonical97`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1395`, `OAI.MUB6.Certificate.MixedSemantics.sound1396`, `OAI.MUB6.Certificate.MixedSemantics.sound1397`, `OAI.MUB6.Certificate.MixedSemantics.sound1399`, `OAI.MUB6.Certificate.MixedSemantics.sound1401`, `OAI.MUB6.Certificate.MixedSemantics.sound1409`, `OAI.MUB6.Certificate.MixedSemantics.sourceEq1094`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound38`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound39`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound40`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound42`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound43`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound72`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound77`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound86`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1780`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1012`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1030`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1123`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1158`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1169`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1205`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1227`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1232`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1335`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1465`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1483`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1490`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1589`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1595`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1598`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1744`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1848`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1882`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1957`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound590`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound601`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound612`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound620`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound621`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound632`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound642`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound644`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound660`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound686`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound745`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound945`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound39`.
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

def raw11Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw11step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw12 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-2, 4, -2]]
def raw113Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw113step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw114 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw114step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw115 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw115Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw115step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw116 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw116Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw116step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw117 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw117Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw117step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw118 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw118Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw118step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw119 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw119Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw119step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw120 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw120Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw120step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw120step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw121 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw121Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw121step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw124 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1135Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1135step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1136 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1136Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1136step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1136step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1136step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1137 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 4, -3]]
def raw1137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1137step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw1137step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1137step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw1137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1138 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 4, -3]]
def raw1138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1138step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw1138step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1139 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 4, -3]]
def raw1139Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1139step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw1139step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw1139step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1140 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1140step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1141 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1141Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1141step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1142 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1142Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1142step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1142step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1142step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1142step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1142step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1143 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1143step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1143step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1144 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1144Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1144step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1145 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1145Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1145step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1145step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1145step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1146 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1146step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1147 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1147Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1147step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1148 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1148Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw1148step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1148step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1148step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1149 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1149step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1150 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1150Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1150step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1151 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1151Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1151step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1151step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1151step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw11352Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11353Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw11353step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw11353step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11354Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11354step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11355Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11355step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11356Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11356step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw11358step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw11358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11359step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11359step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw11365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11365step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw11366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw11367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw11369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw11369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw11370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw11371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw11372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw11374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw11374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw11374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11375 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11375step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11375step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11375step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11375step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11375step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11376step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw11376step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11376step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11376step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11376step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11376step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11377 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11377step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11377step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11377step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11377step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11377step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11377step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11377step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11377step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11378 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw11378step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11378step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11378step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11378step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11379 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw11379step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11379step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11379step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11379step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11379step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw11380step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11380step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11380step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11380step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11380step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11381 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11381step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11381step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11381step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11381step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11381step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11381step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11381step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11381step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11382 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11382step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11382step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11382step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11382step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11384 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11384step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11384step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11385 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11385step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11386 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw11386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11388 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11388step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11388step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11389 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11389Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11389step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11389step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11389step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11389step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11389step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11389step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11389step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11390Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11390step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11390step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11390step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11390step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11390step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11390step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11391 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11391Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11391step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11391step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11391step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11391step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11391step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11391step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw11392 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11392Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11392step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11392step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11392step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11392step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11393 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11393Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11393step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11393step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11393step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11393step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11393step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11393step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11394Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11394step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11394step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11394step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11394step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11394step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11395 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11395Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11395step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11395step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11395step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11395step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11395step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw11395step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11395step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw11395step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw11396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11396step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw11397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11398step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11398step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11398step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11398step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11398step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11398step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11398step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11398step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11399step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11399step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11399step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11399step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11399step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11399step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11400step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11400step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11400step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11400step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11400step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11401step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11401step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11401step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11401step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11401step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11401step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11401step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11401step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11402step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11402step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw11402step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11402step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11402step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11402step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11402step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11402step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11402step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11403step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11403step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11404step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11404step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11405step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11405step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11406step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11406step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11406step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11407step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11407step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw11407step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11407step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw11407step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw11407step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw11407step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11408step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11409step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11410step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11411step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11411step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11412step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11413step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11414step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11415step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11416step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11418step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11418step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11419step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11420step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11421step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw11422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw11422step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11422step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw11422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11422step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11422step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11423step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11423step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11424step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11424step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11425step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11426step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw11427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw11427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11427step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw11427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11428Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11428step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11428step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11428step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11428step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11428step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11428step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11428step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11428step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11428step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11429Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11429step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11429step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11429step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11429step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11429step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11430Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11430step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11430step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11430step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11430step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11430step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11431Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11431step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11431step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11431step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11431step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11431step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11431step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11431step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11431step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11431step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11432Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11432step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11432step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw11432step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11432step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11432step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11432step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11432step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11432step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11432step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11433Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11433step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11433step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11433step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11433step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11433step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11433step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11433step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11433step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11434Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11434step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11434step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11434step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11434step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11434step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11435Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11435step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11435step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11435step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11435step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11435step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11436Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11436step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11436step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11436step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11436step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11436step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11436step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11436step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11436step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11436step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11437Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11437step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11437step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw11437step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11437step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw11437step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11438Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11438step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11438step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11438step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11438step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11438step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11438step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11439Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11439step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11439step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11439step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11439step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11439step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11440Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11440step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11440step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11440step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11440step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11441Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11441step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11441step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11441step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11441step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11441step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11442step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11442step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11442step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11442step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11442step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11443step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11443step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11443step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11443step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11443step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11444step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11444step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11444step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11444step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11445step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11445step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11445step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11445step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11446step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11446step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11446step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11446step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11446step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11447step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11447step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11447step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11447step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11447step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11448step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11448step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11448step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11448step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw11448step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11448step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw11448step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11448step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw11448step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11449step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11449step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11449step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11449step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw11449step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11449step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw11449step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11449step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw11449step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw11450step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw11450step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11450step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw11450step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11451Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11451step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw11451step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw11451step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11451step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw11451step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw11452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw11452step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw11452step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11452step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11452step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11452step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11452step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11453Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11453step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11453step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11453step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw11453step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11453step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11453step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11453step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11453step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11454step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11454step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11454step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw11454step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11454step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw11454step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11454step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw11454step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11455Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11455step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw11455step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11455step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11455step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11455step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11456Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11456step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw11456step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11456step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11456step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11456step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw11457Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw11457step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11457step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw11457step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11457step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw11457step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11457step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11457step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11457step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11457step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11458step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11462step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11463step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11464 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]
def raw11464Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11464step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw11464step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11464step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw11464step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11465step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11465step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11465step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11465step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11466 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11466step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11466step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11466step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11466step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw11467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw11467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw11467step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11467step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw11467step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11467step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11467step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11467step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11467step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11468 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw11468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw11468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw11468step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11468step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11468step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11468step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11468step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw11469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw11469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw11469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11469step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11469step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11469step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11469step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11469step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11469step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11470 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw11470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw11470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11470step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11470step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11470step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11470step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11471step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw11471step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11471step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11471step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11471step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11471step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11472step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11472step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11472step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11472step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11473step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11473step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11473step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11473step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw11474step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11474step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 0, -2]]
def raw11474step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11474step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw11474step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11474step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw11474step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11474step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw11474step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11475step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11475step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11475step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11475step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11475step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11475step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11476step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11476step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11476step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw11479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11479step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![2, 0, -2]]
def raw11479step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11479step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw11479step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw11479step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw11479step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11480step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11480step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11480step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11480step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11480step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11480step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11480step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11484step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11485step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11485step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11485step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11485step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11488step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11489step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11490step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11490step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11490step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11490step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11490step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11490step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11491step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11491step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11492step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11493step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11493step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11494step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11494step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11495step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11495step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw11495step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11495step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11495step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11496step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11496step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11496step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11497Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11497step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11497step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11498Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11498step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11498step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11499Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11499step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11499step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw11500Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw11500step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11500step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw11500step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11500step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw11500step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11501Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11501step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11501step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11501step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11501step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw11501step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11501step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw11501step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11501step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw11501step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11502Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11502step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11502step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11502step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11502step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw11502step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11502step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw11502step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11502step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw11502step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11503Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11503step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11503step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11503step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw11503step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11503step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw11503step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11503step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw11503step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11504Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11504step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11504step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11504step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11504step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw11504step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11504step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw11504step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11504step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw11504step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11504step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw11504step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11505Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11505step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11505step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11505step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 1, -2], ![1, 0, -1]]
def raw11505step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11505step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw11505step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11505step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11505step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11505step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11505step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11506step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11506step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11507Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11507step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11507step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11508step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11508step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11509step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11509step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11509step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11509step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11509step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11509step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11509step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11510step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11510step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11510step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11510step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11510step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11510step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11510step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11510step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11511step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11512step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11513step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11514step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11514step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11514step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11514step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11514step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11514step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11515step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11515step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11515step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11515step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11515step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11515step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11515step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11516step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11516step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11517step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11518step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11519step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11519step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11519step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11519step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11519step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11519step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1152 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-2, 4, -2]]
def raw1152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1152step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw1152step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw1152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1153 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-2, 4, -2]]
def raw1153Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1153step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw1153step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1154 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-2, 4, -2]]
def raw1154Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1154step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw1154step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1154step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1154step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1154step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1155 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw1155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1155step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw1155step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1155step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw1155step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1156 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw1156Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1156step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw1156step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1157 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw1157Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1157step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw1157step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw1157step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1157step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw1157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1158 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1158step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1158step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1158step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1159 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1159Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1159step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1159step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1160 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1160Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1160step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw1160step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1160step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1160step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1160step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1160step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1161 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1161step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1161step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1161step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1162 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1162Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1162step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1163 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1163Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1163step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw1163step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1163step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1163step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1206 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1206step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1206step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1207 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1208 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1208Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw1208step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1208step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1208step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1208step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1209 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 3, -3]]
def raw1209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1209step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1209step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1210 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 3, -3]]
def raw1210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1211 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 3, -3]]
def raw1211Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw1211step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1211step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1211step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1212 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1212step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1213 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1214 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1214Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1214step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1214step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1214step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1215 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1215step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1215step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1216 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1217 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1217Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw1217step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1217step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1217step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1218 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1218step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1218step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1219 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1220 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1220Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw1220step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1220step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1220step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1221 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 4, -3]]
def raw1221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1221step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw1221step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw1221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1222 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 4, -3]]
def raw1222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1222step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw1222step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1223 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 4, -3]]
def raw1223Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1223step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw1223step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1223step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw1223step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1224 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1224step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1225 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1226 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1226Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1226step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1226step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1226step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1226step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1226step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1227 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw1227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1227step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1228 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw1228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1229 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw1229Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw1229step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1229step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1229step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1230 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1230step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1231 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1231Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1231step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1232 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1232Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw1232step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1232step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1232step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1233 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 3, -4]]
def raw1233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1233step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw1233step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw1233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1234 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 3, -4]]
def raw1234Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1234step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw1234step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1235 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 3, -4]]
def raw1235Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1235step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw1235step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw1235step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1236 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1236step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1237 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1237Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1237step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1238 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1238Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw1238step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1238step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1238step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1238step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1239 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 1, -2], ![-1, 3, -2]]
def raw1239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1239step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw1239step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw1239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1240 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 1, -2], ![-1, 3, -2]]
def raw1240Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1240step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw1240step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1241 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 1, -2], ![-1, 3, -2]]
def raw1241Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1241step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw1241step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1241step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1241step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1241step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1242 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 2, -3]]
def raw1242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1242step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw1242step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw1242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1243 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 2, -3]]
def raw1243Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1243step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw1243step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1244 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 2, -3]]
def raw1244Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1244step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw1244step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1244step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1244step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1244step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1245 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1245step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1245step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1246 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1246Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1246step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1247 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw11520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11520step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11520step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11520step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11520step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11520step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11520step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11521step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![2, -1, -1]]
def raw11521step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11521step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw11521step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11522step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw11522step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw11523step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw11524step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw11525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw11525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw11525step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11525step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![2, 0, -2], ![1, 0, -1]]
def raw11525step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11525step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw11525step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw11525step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw11525step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw11525step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw11525step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11526step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11526step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw11526step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11529step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw11530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw11530step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw11530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11530step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw11530step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11531Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11531step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11531step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11531step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw11531step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11532Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11532step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11532step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw11532step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11532step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw11532step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11533Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11533step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11533step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw11533step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11533step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw11533step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11534step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11534step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw11534step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11535step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw11535step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11536step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11536step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw11536step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11536step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw11536step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11537step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11537step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11537step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw11537step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11538step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11538step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw11538step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11539step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11539step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw11539step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11540step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11540step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11540step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11540step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11540step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw11540step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11541step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11541step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11541step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw11541step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11542Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11542step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11542step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11542step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw11542step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11543Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11543step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11543step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11543step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw11543step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11544step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11544step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11544step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11544step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11555step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11583step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11587step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw11592step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11592step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw11593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11594step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11595step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw11597step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw11598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw11598step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11601step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11602step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11603Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11603step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11603step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11604Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11604step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11604step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11604step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11605Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw11605step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw11605step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11605step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw11605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11606Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11606step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11606step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11606step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11606step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11606step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11607Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11607step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11607step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11607step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11607step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11607step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw11608step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11608step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11609Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11609step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11609step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11609step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw11610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw11610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw11610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11611step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11611step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11611step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11611step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11611step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11612step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11612step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11612step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11612step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11612step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11613Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw11613step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11613step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11613step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11613step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11614Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11614step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11614step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11614step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11615Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11615step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11615step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11615step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11615step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11615step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11616step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11616step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11616step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11616step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11616step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11617Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11617step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11617step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11617step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11617step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11617step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11618step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11618step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11619Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11619step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11619step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw11620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11620step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw11621step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11621step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw11621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11621step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw11621step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw11622step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw11622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11622step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11622step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw11623step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11623step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11623step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11623step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11624step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw11625step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11625step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw11626step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw11626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11626step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw11626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw11627step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw11627step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11627step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11627step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11627step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw11628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw11628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11628step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11628step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11629step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11629step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11629step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11630step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw11631step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11631step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11631step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11632step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11632step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11632step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11632step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11632step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11632step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11633step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11633step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11633step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11633step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11633step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11634Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11635Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11636Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11636step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11637Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11637step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11638Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11638step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11640 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]
def raw11640Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11640step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]
def raw11640step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11640step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw11640step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11641step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11647step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw11648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw11649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11650step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11652step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11655Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11656Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11656step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11658Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11658step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11659Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11659step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11660 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11660step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11660step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11660step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11661 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11661step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11661step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11662 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11662step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11663 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11663step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11663step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11664 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11664step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11664step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11664step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11665 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11665step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11665step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11665step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11665step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11666 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11666step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11666step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11666step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11666step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11667step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11668 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11668step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11668step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11669 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11669step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11670 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw11670step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11670step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11670step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11670step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11671 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11671step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11672 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11672step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11673 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11673step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11674 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11674step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11675 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11675step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11675step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11675step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11675step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11676 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11676step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11676step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11677 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11677step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11678 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11678step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11678step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11679 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11679step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11680 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11680step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11680step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11680step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11680step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11681 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11681step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11681step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11681step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11682 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11682step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11683 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11683step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11684 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw11684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11684step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11684step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11685 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw11685step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11685step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11685step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11685step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11686 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw11686step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11686step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw11686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11687 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11687step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11688 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11688step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11688step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11689 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw11689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11689step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11689step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11690 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11691 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11692 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11693 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11694 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11695 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11696 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11696step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11696step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11697 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11698 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11699 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11700 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11701 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11702 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11702Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11702step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11703 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11704 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11704step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11705 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11706 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11707 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11707step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11707step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11708 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11708step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11709 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11709step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11710 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11710step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11711 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11711step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11712 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11712step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11713 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11713step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11714 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw11714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11715step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11716 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11716step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11717 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11717step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11717step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11718 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11718Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw11718step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11719 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw11719Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw11719step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11720 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11720step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11720step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11720step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11721 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11721step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11722 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11722step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11723 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11723step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11723step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11724 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11724step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11724step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11725step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11725step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11725step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11726 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11726step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11726step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11726step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11726step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11727 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11727step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11728 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11729 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw11730step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw11730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11730step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw11730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11731 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11731step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11731step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11732 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11732step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11732step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11733 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11733step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11733step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11734 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11735step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11735step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11735step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11736 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11737 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11738 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11738step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11739 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11739step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11739step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11740 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11740step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11740step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11741 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11741step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11742 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11743 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11743step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11744 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw11744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11744step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11744step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11745 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11745step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11746 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw11746step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw11746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11747 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw11747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw11747step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11748 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11748step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11748step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11749 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw11749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11749step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11750 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11751 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11752 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11753 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11753step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11753step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11754 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11755 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11756 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw11756Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11756step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw11756step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11756step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw11756step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11756step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw11756step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11757 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw11757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11757step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11758 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11759 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11760 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw11760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11761 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw11761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11762 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw11762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11762step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11763 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw11763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11764 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11764step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11765 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11765step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11766 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11766step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11767 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11767step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11768 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11769 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11769step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11769step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11770 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11771 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw11771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw11802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11802step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11804step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11805step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11809step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11810step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11810step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11811Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11812Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11812step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11813Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11813step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11814step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11814step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11815step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11817Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11817step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11818Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11819Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11820Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw11820step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11821Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw11821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11822Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11823Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11823step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11825Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw11825step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw11826Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw11826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11828Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11830step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11831step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11832Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11832step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11832step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11832step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11833Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11833step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11833step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11833step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11834Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11834step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11834step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11834step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11834step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11834step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11835Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11835step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11835step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11835step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11835step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11835step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11835step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11836Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw11836step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11836step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11836step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11837Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11837step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11837step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11837step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11837step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11838Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11838step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11838step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11838step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11839Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11839step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11839step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11839step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11839step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11839step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11839step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11840Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11840step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11840step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11840step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11840step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11840step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11841Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw11841step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11841step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11841step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11841step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11842Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11842step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11842step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11842step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11842step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11843Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11843step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11843step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11843step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11843step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11843step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11844Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11844step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11844step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11844step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11844step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11844step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11844step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11845Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11845step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11845step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11845step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11845step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11845step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11846Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11846step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11846step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11846step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11846step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11847Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11847step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11847step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11847step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11847step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11847step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11848Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw11848step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11848step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11848step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11848step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11849Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11849step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11849step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11849step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11849step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11850Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw11850step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw11850step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11850step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11850step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11850step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11851Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw11851step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11851step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11851step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11851step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11852Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11852step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11852step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11852step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11853Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw11853step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11853step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11853step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11854Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11854step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11854step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11854step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11855Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw11855step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw11855step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11855step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11855step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11855step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11855step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw11856Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw11856step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11856step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11856step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11857Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11857step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11857step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11857step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11857step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11858Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11858step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11858step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11858step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11859Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11859step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11859step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11859step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11859step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11860Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11860step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11860step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11860step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11860step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11860step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11861Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11861step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11861step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11861step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11861step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11861step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11868 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![0, 0], ![0, 0], ![1, -1]]
def raw11868Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11868step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![0, 0], ![1, -1]]
def raw11868step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11868step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw11868step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11868step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw11868step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw11874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw11877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw11882step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11882step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw11882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11884step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11884step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11885step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11886step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11886step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11886step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11886step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11886step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11887step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11888step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11888step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11889step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11890step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11891step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11891step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11892step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11893step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11893step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11893step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw11894step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw11894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw11895step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw11895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11896step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11896step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11897step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11897step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11898step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11898step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11899step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw11900step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw11900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw11901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11901step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11901step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11901step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11902step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11903step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw11904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11904step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw11905step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw11905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw11906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11906step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11906step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11906step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11907step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11907step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11908step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11909step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11909step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw11910step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11910step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw11910step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw11911step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw11911step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11914step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11915step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11916step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11921step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11926step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw11930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw11931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11933step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11934step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw11935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw11936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11938step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11939Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11939step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11940Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw11940step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11941Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw11941step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11942step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11942step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11942step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11942step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11943step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11943step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11943step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11944step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11944step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11945step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11945step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11945step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11945step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11946step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11946step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11946step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11946step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11947step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11947step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11947step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11947step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw11948step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11948step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw11948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11948step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw11948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11949step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11949step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11949step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11950step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11951step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw11951step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11951step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11951step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11951step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11951step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw11952step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11952step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw11953step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw11953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw11954step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw11954step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw11955step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw11955step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11956step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw11956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw11956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11957step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11957step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11957step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11957step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11958step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11958step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11958step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11959step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11959step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11959step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11960step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11960step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11960step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw11961step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11961step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11961step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11961step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11962step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11962step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11962step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11963Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11963step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11963step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11963step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11963step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11964Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11964step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11964step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11964step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11964step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11965Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11965step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11965step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11965step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11965step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw11966Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11966step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11966step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11966step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11966step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11966step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11967Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw11967step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11967step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11967step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11967step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11968Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw11968step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11968step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11968step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11969Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw11969step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11969step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11969step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11969step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11970Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw11970step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11970step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11970step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11970step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11971Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw11971step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11971step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11971step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw11973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11974Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11977Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11977step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw11977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11978 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![1, -1], ![1, -1], ![0, 0]]
def raw11978Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11978step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![1, -1], ![1, -1]]
def raw11978step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11978step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw11978step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw11979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11980Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11980step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw11984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11987step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw11987step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11992Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11992step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11993step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw11995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11998 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11998step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11998step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11998step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11999 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11999step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11999step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11999step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12000 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12000step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12000step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12000step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12001 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12001step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12001step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12001step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12002 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12002step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12002step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12002step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12002step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12003 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12003step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12003step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12004 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12004step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12004step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12005 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12005step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12005step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12006 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw12006step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12006step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw12006step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12006step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw12006step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12007 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12007step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12007step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12008 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12008step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12008step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12009 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12009step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12009step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12009step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12010 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw12010step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12010step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12010step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12010step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12011 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12011step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12011step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12011step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12011step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12011step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12012 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12012step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12012step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12012step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12013 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12013step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12013step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12013step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12014 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12014step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12014step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12014step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12015 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12015step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12015step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12015step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12015step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12015step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12016 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12016step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12016step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12016step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12016step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12017 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12017step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12017step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12017step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12017step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12018 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12018step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12018step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12018step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12019 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12019step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12019step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12020 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12020Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12021 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12021Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12022 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12022Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12023 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12023Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12024 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12024Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12024step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12025 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12025Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12025step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12026 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12026Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12026step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12027 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12027Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12027step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12028 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12028Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw12028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12029 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12029Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw12029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12030 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12030Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12031 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12031Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw12032 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12032Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw12032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12033 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12033Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12034 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12034Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12035 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12035Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12036 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12036Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12037 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12037Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12038Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12039 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12040 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12041 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12042 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12042Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12042step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12043 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12043Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12043step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12043step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12044 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12044Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12044step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12044step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12045 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12045Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12045step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12045step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12046 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12046Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12046step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12046step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12046step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12047 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12047Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12047step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12047step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12047step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12048 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12048Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12048step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12048step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12048step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12049 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12049Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12049step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12049step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12050 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12050Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw12050step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw12050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12051 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12051Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12051step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12052 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12052Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12052step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12053 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12053Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12053step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12054 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12054Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12054step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12055 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12055Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw12055step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12055step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12055step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12055step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12056 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12056Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12056step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12056step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12057 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12057Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12057step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12058Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12058step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12059 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12059Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw12059step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12059step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12059step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12059step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12059step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12060Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12060step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12061 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12061Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12061step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12061step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12062 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12062Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12062step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12062step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12063Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12063step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12064 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12065 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12066 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12067 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12067step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12068step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12069 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12069step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12070 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12070step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12070step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12071 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw12071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw12071step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12072step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12073step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12074 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12075 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12076 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12077 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12077step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12078 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw12082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12082step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12082step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12082step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![1, 1, -2]]
def raw12082step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12082step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw12082step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12082step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw12082step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12082step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw12082step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12083step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12083step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12083step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12083step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12084step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12084step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12084step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw12086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12086step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12088step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12088step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw12090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12092step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12092step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12092step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12092step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12094step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw12095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12095step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -2, 0], ![1, 1, -2]]
def raw12095step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12095step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw12095step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12096step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12096step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12096step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12097step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12097step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12097step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12097step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12099step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw12100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw12100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw12100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12100step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12101Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12101step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12102Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12102step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12103step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12103step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![1, 1, -2]]
def raw12103step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12103step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw12103step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw12104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12104step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12104step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12104step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![1, 1, -2]]
def raw12104step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12104step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw12104step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12105step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12105step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12106step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12108step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12108step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12108step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12108step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw12109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12109step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12110step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12111step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12112step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12113step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12113step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12113step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw12114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12114step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12114step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12116step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12116step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12116step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12116step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12117step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw12119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12119step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12119step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12119step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -2, 0], ![1, 1, -2]]
def raw12119step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12119step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw12119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12120step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12120step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw12120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12121step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12121step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12121step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12122step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12123Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12123step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12124Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12124step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12124step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12124step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -2, 0], ![1, 1, -2]]
def raw12124step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12124step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw12124step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw12125Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw12125step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw12125step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12125step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw12125step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12126Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12126step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12126step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12126step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12126step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12127Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12127step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12128Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12128step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12128step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12129Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12129step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12129step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12129step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw12129step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12129step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw12129step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw12130Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12130step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12130step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12130step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12130step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw12130step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12130step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw12130step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12131step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12131step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12132step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12132step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12133step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12133step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12133step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12133step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12133step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12134step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12134step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12134step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12135step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12135step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12136step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12137step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12137step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12137step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12138step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12138step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12139step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12139step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12140step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12141step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12141step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12141step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12142step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12142step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12143step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12143step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12143step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12143step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12143step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12143step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12144step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12145step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12145step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12146step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12146step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12146step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12146step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12147step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12147step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12147step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12147step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12147step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12147step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12148step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12148step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12148step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12148step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12148step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12149step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12150step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12150step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw12151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw12151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw12151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12151step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12151step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12151step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12151step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12152step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12152step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12152step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12153Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12153step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12154Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12154step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12154step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12155Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12155step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12155step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12155step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12155step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12155step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12156step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12156step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12157step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12157step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12157step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw12157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12158step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12159step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw12160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12160step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12161step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12162step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12163step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12164step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12166step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12166step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12166step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12168step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12168step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12168step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12171step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12171step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12172step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12173step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12176step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12176step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12176step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw12177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw12177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12177step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw12177step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12177step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12178step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12178step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw12178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12179step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw12179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw12180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12181step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw12182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw12182step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw12182step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12183 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12183step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12183step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12183step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12184 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12184step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12184step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12184step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12184step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12185 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12185step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12185step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12185step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12185step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12185step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12185step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12186 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12186step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12186step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12186step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12186step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12187 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12187step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12187step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12187step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12187step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12187step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12187step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12188 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12188step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12189 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12189step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12189step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12190 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12190step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12190step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12191 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12191step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12191step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12192 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12192step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12192step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12192step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12192step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12192step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12192step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12192step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12192step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12192step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12193 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12193step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12193step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12193step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12194 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12194step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12194step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12194step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12194step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12194step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12194step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12195 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12195step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12195step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12195step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12195step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12195step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12196 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12196step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12196step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12196step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12196step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12196step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12196step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12196step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12196step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12197 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12197step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12197step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12197step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12198 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12198step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12198step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12198step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12198step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12198step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12198step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12199 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12199step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12199step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12199step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12199step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12199step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12200 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12200step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12200step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw12200step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12200step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw12200step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12200step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw12200step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12201 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw12201step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw12201step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12202 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12202step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12202step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12202step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12202step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12202step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12203 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12203step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12203step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12203step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12203step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12203step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12203step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12204 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12204step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12205 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12205step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12205step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12205step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12205step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12205step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12206 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12206step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12206step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12206step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12206step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12206step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12206step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12207 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12207step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12207step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12207step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12207step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12207step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12207step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12208 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12208step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12208step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12208step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12209 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12209step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12210 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12210step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12210step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12210step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12211 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12211step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12211step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12211step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12212 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12212step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12212step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12212step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12213 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12213Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12213step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12213step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12213step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12213step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12213step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12213step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12214 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12214step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12214step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12215 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12215Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12215step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12215step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12215step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12215step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12215step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12215step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12215step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12216 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12216Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12216step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12216step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12216step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12216step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12216step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12216step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12217 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12217Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12217step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12217step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12217step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12217step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12217step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12217step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12217step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12217step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12218 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12218Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12218step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12218step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12218step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12219 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12219Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12219step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12219step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12219step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12219step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12219step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12219step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12219step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12220 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12220step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12220step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12220step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12220step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12220step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12220step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12220step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12221 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12221Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12221step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12221step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw12221step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12221step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw12221step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12222 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12222step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12222step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12222step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12223 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12223Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12223step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12223step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12223step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12223step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12223step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12223step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12223step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12224 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12224Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12224step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12224step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12224step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12224step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12224step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12224step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12225 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12225step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw12225step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12225step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw12225step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12226 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw12226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12226step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12226step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12227 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12227step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12227step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12227step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12227step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12227step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12227step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12228 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12228step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12228step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12228step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12228step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12228step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12228step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12229 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12229step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12229step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12229step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12229step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12229step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12229step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12232step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12232step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12232step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12232step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12260step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12261step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12262step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12263step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12263step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12264step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12266step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12267Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12268Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12268step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12269Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12270Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12270step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12270step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12272Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12272step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12273Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12273step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12273step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12273step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12273step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12274step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12275step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12275step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12276step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12277Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12277step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12277step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw12278step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw12278step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12278step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw12278step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12279Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12279step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12279step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12280Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12280step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw12280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12281Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw12281step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12282Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12282step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw12282step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12283Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12283step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12283step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw12284Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw12284step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw12284step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12285Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12285step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12285step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12286Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12286step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12287step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12287step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw12288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12288step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw12289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12289step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12289step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12289step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12289step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12290step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12290step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12290step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12291step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw12291step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12291step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12291step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12291step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12292step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12292step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12292step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12292step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12292step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12293Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12293step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12293step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12293step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12293step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12293step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12293step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12293step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12293step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12294step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw12294step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12294step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12294step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12294step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12295step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12295step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12295step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw12296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12296step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12296step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12297step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12297step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12297step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12297step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12298step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12298step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12298step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12298step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12299Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw12299step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12299step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12299step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12299step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12300step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12300step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12300step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12300step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12300step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12300step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12301step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12301step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12301step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12301step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12302step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12302step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12302step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12302step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12303step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12303step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12303step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12303step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12303step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12303step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12303step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12303step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12304step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12304step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12304step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12304step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12304step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12304step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12305step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw12305step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12305step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw12305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12306step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12306step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12307Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12307step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw12307step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12307step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw12307step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw12308step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw12308step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12308step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw12308step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12308step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw12308step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12309Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12309step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw12309step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw12309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12310step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw12310step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw12310step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12310step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw12310step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw12311step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12311step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12311step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12311step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12312step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw12312step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12312step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12312step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12312step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12313step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw12313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12313step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12313step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12313step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw12314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw12314step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw12314step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12314step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12314step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12314step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12315Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12315step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw12315step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw12315step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12315step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw12315step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw12316step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12316step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12316step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12317step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw12317step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12317step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12317step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12317step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12318step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw12318step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12318step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12318step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12318step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw12319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12319step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12319step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12319step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12319step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw12319step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12319step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12319step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12319step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12319step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw12323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12324step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw12325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12326 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![0, 0], ![2, -2]]
def raw12326Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12326step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![2, -2]]
def raw12326step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12326step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw12326step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12326step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw12326step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw12329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw12333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12336step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw12340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12343step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12343step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12343step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12344step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12345step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12345step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12346step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12346step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12346step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12347step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12347step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12347step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12348step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12348step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12349step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12349step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12350step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12350step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12350step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12351step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12351step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12352step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12352step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12352step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12353step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12354step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12354step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12355step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12355step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12355step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw12356step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12356step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw12356step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12357step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12357step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12358step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12358step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12359step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12359step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12360step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12360step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12360step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12361step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12361step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12361step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12361step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12362step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12362step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12363step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12363step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12364step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12364step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12364step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12365step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12365step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12366step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12366step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12366step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12366step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw12367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw12367step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12367step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12367step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12367step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12368step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12368step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12368step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12368step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12369Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12369step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12369step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12370step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12370step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12370step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12370step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12371step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw12371step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12371step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw12371step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw12372Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw12372step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12372step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12372step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12377step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12382step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12385step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw12386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12389Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12389step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12390step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12390step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12391step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12391step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12392step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12393step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw12397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw12397step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12398step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12400step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12401step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw12401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw12402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw12402step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw12402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12403Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12403step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12404step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12404step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12405Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12405step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12405step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12405step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12405step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12406step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12406step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12406step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12406step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12407Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12407step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12407step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12408step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12408step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12408step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12409Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12409step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12409step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12409step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12409step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12410step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12410step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12410step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12411Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12411step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12411step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12411step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw12412step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12412step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12412step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12413Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12413step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw12413step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12413step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12413step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12413step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12414Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw12414step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12414step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12414step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12414step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12415Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12415step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw12415step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12415step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12415step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12415step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12415step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw12416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12416Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12416step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw12416step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12416step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12416step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12416step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12416step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12417Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12417step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12417step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12417step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12417step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12417step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12418Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12418step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw12418step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12418step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12418step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12418step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12419Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw12419step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12419step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12419step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12420Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12420step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw12420step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw12420step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12420step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw12420step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12421Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12421step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw12421step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12421step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12421step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12421step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12422Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12422step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw12422step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12422step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12422step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12422step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12423Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12423step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw12423step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12423step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12423step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12423step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12424Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw12424step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12424step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12424step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12424step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12425Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12425step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw12425step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12425step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12425step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12425step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12426Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12426step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw12426step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12426step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12426step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12426step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw12427Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw12427step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw12427step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12427step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12427step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12427step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12428Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12428step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw12428step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw12428step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12428step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw12428step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12429Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12429step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12429step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12430Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12430step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw12430step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw12430step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12431Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12431step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw12431step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw12431step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw12432Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw12432step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12432step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12432step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12433step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12436step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12439 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2], ![1, -1], ![-1, 1]]
def raw12439Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12439step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![-1, 1]]
def raw12439step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12439step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw12439step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12439step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw12439step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw12453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12463 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12463step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12463step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12463step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12467 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12467step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12467step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12467step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12473 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12473step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12477 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12477Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12477step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12477step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12477step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12477step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12477step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12478 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12478Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12478step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end


