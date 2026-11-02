-- Prove2me | Definitions.Def_OAIQ106D007
-- name    : OAIQ106D007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T11:59:51.636036+00:00
-- url     : https://prove2.me/theorems/666398a3-754a-4131-bcc8-c96d8eaf6424
-- title:
--   Definitions bundle OAIQ106D007 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7385 declarations of OpenAI's Lean: 7385 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw12478step1`, `OAI.MUB6.Certificate.MixedSemantics.raw12478step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw12479`, `OAI.MUB6.Certificate.MixedSemantics.raw12479Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw12479step0`, `OAI.MUB6.Certificate.MixedSemantics.raw12479step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw12479step1`, `OAI.MUB6.Certificate.MixedSemantics.raw12479step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1247Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1247step0`, `OAI.MUB6.Certificate.MixedSemantics.raw1247step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1247step1`, `OAI.MUB6.Certificate.MixedSemantics.raw1247step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1247step2`, `OAI.MUB6.Certificate.MixedSemantics.raw1247step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1248`, `OAI.MUB6.Certificate.MixedSemantics.raw12480`, `OAI.MUB6.Certificate.MixedSemantics.raw12480Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw12480step0`, `OAI.MUB6.Certificate.MixedSemantics.raw12480step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw12480step1`, `OAI.MUB6.Certificate.MixedSemantics.raw12480step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw12481`, `OAI.MUB6.Certificate.MixedSemantics.raw12481Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw12481step0`, `OAI.MUB6.Certificate.MixedSemantics.raw12481step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw12482`, `OAI.MUB6.Certificate.MixedSemantics.raw12482Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw12482step0`, `OAI.MUB6.Certificate.MixedSemantics.raw12482step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw12482step1`, `OAI.MUB6.Certificate.MixedSemantics.raw12482step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw12483`, `OAI.MUB6.Certificate.MixedSemantics.raw12483Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw12483step0`, `OAI.MUB6.Certificate.MixedSemantics.raw12483step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw12484`, `OAI.MUB6.Certificate.MixedSemantics.raw12484Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw12484step0`, `OAI.MUB6.Certificate.MixedSemantics.raw12484step0Labels` and 7345 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical1`, `MutuallyUnbiased_MixedSemantics_Canonical10`, `MutuallyUnbiased_MixedSemantics_Canonical100`, `MutuallyUnbiased_MixedSemantics_Canonical101`, `MutuallyUnbiased_MixedSemantics_Canonical102`, `MutuallyUnbiased_MixedSemantics_Canonical103`, `MutuallyUnbiased_MixedSemantics_Canonical104`, `MutuallyUnbiased_MixedSemantics_Canonical105`, `MutuallyUnbiased_MixedSemantics_Canonical106`, `MutuallyUnbiased_MixedSemantics_Canonical9`, `MutuallyUnbiased_MixedSemantics_Canonical97`, `MutuallyUnbiased_MixedSemantics_Canonical98`, `MutuallyUnbiased_MixedSemantics_Canonical99`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1409`, `OAI.MUB6.Certificate.MixedSemantics.sound1410`, `OAI.MUB6.Certificate.MixedSemantics.sound1411`, `OAI.MUB6.Certificate.MixedSemantics.sound1412`, `OAI.MUB6.Certificate.MixedSemantics.sound1413`, `OAI.MUB6.Certificate.MixedSemantics.sound1414`, `OAI.MUB6.Certificate.MixedSemantics.sound1416`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound22`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound40`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound42`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound43`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound45`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound84`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound89`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero733`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1009`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1012`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1123`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1158`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1169`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1205`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1227`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1232`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1335`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1428`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1436`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound145`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1465`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1471`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1483`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1490`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1569`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1571`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1589`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1593`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1595`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1598`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1657`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1848`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound660`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound682`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound686`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound688`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound693`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound712`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound721`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound728`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound745`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound746`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound969`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984`, `OAI.MUB6.Certificate.MixedTargetSemantics.allKeyMoments`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound28` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound43`.
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

def raw12Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw12step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw12step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-2, 4, -2]]
def raw124Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw124step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw124step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw125 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw125Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw125step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw126 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw126Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw126step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw127 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw127Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw127step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

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

def raw128 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw128Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw128step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw128step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw129 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw129Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw129step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw130 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw130Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw130step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw130step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw131 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw131Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw131step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw132 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw132Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw132step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw132step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw133 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw133Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw133step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw133step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw134 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw134Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw134step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw135 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw135Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw135step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw136 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1280 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 4, -2]]
def raw1280Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1280step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw1280step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1280step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw1280step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1280step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw1280step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1281 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1281step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1282 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1282Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1282step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1283 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1283Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1283step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1283step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1283step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1284 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw1284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1284step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1284step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1285 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw1285Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1285step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1285step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1286 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw1286Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1286step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw1286step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1286step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1286step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1287 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw1287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1287step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1287step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1287step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1288 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw1288Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1288step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1288step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1289 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw1289Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1289step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw1289step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1289step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1289step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1289step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1290 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 3, -4]]
def raw1290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1290step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw1290step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1290step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw1290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1291 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 3, -4]]
def raw1291Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1291step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw1291step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1292 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 3, -4]]
def raw1292Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1292step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw1292step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1292step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw1292step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1293 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw1293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1293step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1293step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1294 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw1294Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1294step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1295 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw1295Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1295step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1295step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1296 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw1296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1296step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1296step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1296step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1297 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw1297Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1297step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1297step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1298 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw1298Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1298step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw1298step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw1298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1298step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw1298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1299 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1299step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1299step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1299step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1300 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1300Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1300step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1300step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1301 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1301Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1301step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw1301step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1301step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1301step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1302 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1302step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1302step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1302step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1303 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1303Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1303step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1303step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1304 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1304Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1304step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw1304step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw1304step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1304step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw1304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1305 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-2, 3, -1]]
def raw1305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1305step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw1305step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1305step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw1305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1306 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-2, 3, -1]]
def raw1306Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1306step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw1306step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1307 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-2, 3, -1]]
def raw1307Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1307step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]
def raw1307step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1307step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw1307step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1307step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw1307step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1308 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 2, 0], ![1, 2, -3]]
def raw1308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1308step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw1308step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1308step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw1308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1309 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 2, 0], ![1, 2, -3]]
def raw1309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1309step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw1309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1310 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 2, 0], ![1, 2, -3]]
def raw1310Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1310step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw1310step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1310step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw1310step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1310step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw1310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1311 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1311step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1311step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1311step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1312 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1313 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1313Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1313step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1313step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1313step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1313step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1314 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1314step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1314step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1315 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1316 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1316Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 2, -4]]
def raw1316step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 2, -4]]
def raw1316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1317 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1317step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1318 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1319 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1319Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1319step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1319step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1319step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1320 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1320step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1320step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1321 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1322 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1322Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1322step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1322step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1322step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1323 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1323step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1323step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1324 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1325 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1325Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1325step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1325step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1326 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1326step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1326step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1327 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1328 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1328Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1328step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1328step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1328step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1329 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 2, -1], ![0, 3, -3]]
def raw1329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1329step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw1329step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw1329step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1330 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 2, -1], ![0, 3, -3]]
def raw1330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1330step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw1330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1331 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 2, -1], ![0, 3, -3]]
def raw1331Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1331step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![2, -1, -1], ![2, 2, -4]]
def raw1331step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![2, -1, -1], ![2, 2, -4]]
def raw1331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1332 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 2, -2], ![-1, 3, -2]]
def raw1332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1332step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw1332step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw1332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1333 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 2, -2], ![-1, 3, -2]]
def raw1333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1333step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw1333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1334 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 2, -2], ![-1, 3, -2]]
def raw1334Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1334step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw1334step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw1334step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw1334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1335 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1335step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1335step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1335step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1336 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1337 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1337Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw1337step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1337step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw1337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1338 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1338step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1339 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1340 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1340Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1340step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1340step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1340step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1340step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1341 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1341step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1341step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1341step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1342 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1343 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1343Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1343step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1343step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1343step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1343step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1343step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1344 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1344step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1344step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1344step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1344step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1345 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1346 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1346Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1346step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1346step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1346step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1346step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1347 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw1347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw1347step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw1347step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1348 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw1348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw1348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1349 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw1349Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw1349step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw1349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1350 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1350step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1350step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1351 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1352 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1352Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw1352step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw1352step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw1352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1353 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1353step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1353step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1353step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1354 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1355 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1355Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1355step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1355step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1355step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1355step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1355step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1356 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1356step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1356step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1357 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1358 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1358Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1358step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1359 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1359step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1359step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1360 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1361 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1361Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1361step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1361step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1361step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1361step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1362 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1362step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1362step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1363 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1364 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1364Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1364step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1364step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1364step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1364step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1365 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1365step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1365step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1366 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1367 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1367Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1367step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1368 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw12800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12800Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12800step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12801Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12802step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12804step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12805step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12807step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12808step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw12808step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12809step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12809step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw12809step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12810step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12810step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12811Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12812Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12812step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12813Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12813step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12813step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw12814step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw12814step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12814step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12815step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12817Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12817step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12818Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12818step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw12818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0]]
def raw12819Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw12819step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12819step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw12819step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12819step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12819step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12820Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12820step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12821Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12822Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12822step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12822step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12823Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12823step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw12823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw12824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw12824step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw12824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12825Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12825step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12825step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12826Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12826step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12826step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12826step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12826step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12826step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12826step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12827Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12827step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12827step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12827step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12827step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12827step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12828Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12828step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12828step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12829Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12829step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12829step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12829step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12829step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12829step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12829step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12830Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12830step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12830step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12830step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12830step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12831Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12831step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12831step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12831step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12831step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12831step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12832Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12832step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12832step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12832step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12833Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12833step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12833step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12833step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12834Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12834step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12834step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12834step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12834step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12834step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12835Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12835step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw12835step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12835step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw12835step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12835step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw12835step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12836Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12836step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12837Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12837step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw12837step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw12837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12838Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12838step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12838step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12838step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12839Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12839step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12839step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12839step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw12839step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12839step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw12839step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12840Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12840step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw12840step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12840step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12840step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12840step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12841Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw12841step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12841step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12841step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12841step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12842Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12842step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw12842step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12842step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12842step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12842step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12843Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12843step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw12843step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12843step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12843step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12843step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12843step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12844Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw12844step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw12844step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12844step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw12844step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12844step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw12844step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12844step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw12844step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12845Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12845step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw12845step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12845step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12845step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12845step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12846Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw12846step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12846step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12846step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12846step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12847Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12847step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw12847step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12847step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12847step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12847step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12847step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12848Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12848step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw12848step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12848step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12848step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12848step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0]]
def raw12849Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw12849step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12849step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw12849step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12849step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw12849step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12849step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12849step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12849step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12849step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12850Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12850step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw12850step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw12850step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12850step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw12850step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12851Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw12851step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw12851step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12851step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw12851step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12852Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12852step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw12852step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12852step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12852step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12852step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12853Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12853step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw12853step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12853step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw12853step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12853step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw12853step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw12854Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw12854step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw12854step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw12854step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12854step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw12854step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12857Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12858Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12858step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12859Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12859step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12860step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12861 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![2, -2], ![1, -1], ![0, 0]]
def raw12861Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12861step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![2, -2], ![1, -1]]
def raw12861step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12861step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw12861step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12861step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw12861step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw12871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12883 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12883step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12883step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw12887step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw12887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12891 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw12891step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12891step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12891step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12891step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12894 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12894step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12895 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12895Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12895step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12896 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12896Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12896step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw12896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12897 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12897Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12897step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw12897step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12898 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12898Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12899Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw12899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12900 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12900Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw12900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12901 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12901Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw12901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12902 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12902Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12902step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw12902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw12902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12903Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12903step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-3, 1, 2]]
def raw12903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12903step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw12903step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12904 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12904Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12904step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw12904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12904step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw12904step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12905Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12905step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw12905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12905step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12905step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12906 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12906Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12906step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12907 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12907Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12907step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw12907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12908 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12908Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12908step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12911 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12911Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12911step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12911step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12911step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12915 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12915Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12915step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12915step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12919 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12919Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12919step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12919step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12922 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12922Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12922step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12922step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12922step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12923 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw12923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12924 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw12924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12925 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12925step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12925step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12926 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw12926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12927 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw12927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw12928 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw12928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12928step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12928step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12929 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw12929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12929step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12929step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12930 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw12930step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12930step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw12930step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12931 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw12931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12932 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw12932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12932step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12933 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12933Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12933step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12933step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12933step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12933step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12934 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12934step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw12934step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12935 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12935step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12935step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12935step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12936 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12936step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12936step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12936step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12937 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12937step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw12939step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12939step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12939step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12939step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12940step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12940step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12940step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12940step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw12941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12941step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12941step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12941step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12941step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw12942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12942step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12942step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw12959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12959step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw12998step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12998step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12998step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12998step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12998step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13000step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13000step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13000step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13000step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13001step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13001step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13001step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13001step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13001step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13002step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13002step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13002step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13002step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13003step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13003step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13003step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13004step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13004step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13005step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13005step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13006step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13006step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13006step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13007step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13007step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13008step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13008step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13008step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13008step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13009step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13009step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13009step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13010step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13010step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13010step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13011step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13011step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13011step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13012step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13012step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13013step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13013step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13014step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13014step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13014step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13015step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13015step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13015step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13016step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13016step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13017step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13017step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13018step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13018step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13019step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13019step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13020step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13020step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13021step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13021step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw13022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw13022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13022step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13022step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13023step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13023step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13024step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13024step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13024step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13025step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13025step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13025step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13026step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13026step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13026step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw13027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw13027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13027step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13027step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13028Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13028step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13028step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13028step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13029Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13029step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13029step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13029step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13029step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13029step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13030Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13030step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13030step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13030step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13030step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13030step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13031Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13031step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13031step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13031step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13031step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13031step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13032Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13032step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13032step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13032step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13032step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13032step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13033Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13033step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13033step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13033step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13033step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13033step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13034Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw13034step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13034step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13034step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13035Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13035step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13035step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13035step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13036Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13036step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13036step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13036step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13037Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13037step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13037step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13037step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13037step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13038Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13038step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13038step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13038step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw13038step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13038step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw13038step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13039Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw13039step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw13039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13040Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13040step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13040step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13041Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13041step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13041step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13041step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13042Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13042step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13042step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13042step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13043Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13043step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13043step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13043step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13043step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13043step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13044Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13044step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13044step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13044step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13044step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13045Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13045step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw13045step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw13045step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13045step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw13045step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13046Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13046step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13046step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13046step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13046step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13046step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13047Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13047step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13047step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13047step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13047step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13047step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13048Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13048step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13048step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13048step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13048step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13048step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13049Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13049step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13049step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13049step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13050Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13050step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw13050step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw13050step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13050step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw13050step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13051Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13051step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13051step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13051step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13051step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13051step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw13052Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw13052step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13052step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13052step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13052step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13053Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13053step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13053step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13053step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13053step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13053step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13054Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13054step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13054step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13054step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13054step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13055Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13055step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw13055step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw13055step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13055step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw13055step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw13056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13056Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13056step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13056step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13056step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13056step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13056step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13056step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw13057Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw13057step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13057step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13057step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13057step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13057step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw13059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13061step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13063step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13064 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw13064Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13064step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw13064step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13064step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw13064step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -3, 1]]
def raw13065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13069 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13069step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13069step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13069step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13070 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13070step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13070step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13071 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw13071step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13071step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13071step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13071step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13072step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13072step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13073step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13073step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13074 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw13074step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw13074step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13074step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw13074step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13075 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw13075step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13075step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13075step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13075step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13075step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13076 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw13076step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13076step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13076step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13076step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13077 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13077step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13077step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13077step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13077step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13078 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13078step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13078step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13079step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13079step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13080 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13080step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13080step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13080step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13080step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13081 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13081step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13081step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13081step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13082 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13082Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13082step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13083 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13083Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13083step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13083step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13083step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13084 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13084Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13084step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13084step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13085 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13085Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13085step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13086 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13086Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13086step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13087 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13087Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13087step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13088 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13088step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13088step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13089 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13089step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw13089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw13089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13090 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13090step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw13090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw13090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13091 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13091step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw13091step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw13091step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13092 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13092step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13092step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13093 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13093step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13094 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13094step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13094step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13094step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13095 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13095step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13095step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13096 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13096step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13096step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13097 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13097step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13097step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13097step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13098 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13098step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13098step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13098step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13098step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13159Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw13159step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13159step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13159step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13159step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13159step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13160Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw13160step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13160step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13160step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13160step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13160step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13161Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13161step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13161step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13161step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13161step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13161step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13162Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13162step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13162step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13162step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13162step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13163Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw13163step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13163step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13163step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13163step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13164step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13164step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13164step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13164step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13165Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13165step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13165step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13165step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13165step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13166step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13166step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13166step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13167Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13167step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13167step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13167step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13167step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13167step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13168step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13168step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13168step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13168step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13169Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13169step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13169step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13169step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13169step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13170step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13170step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13170step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13170step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13171Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13171step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13171step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13171step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13172step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13172step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13172step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13172step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13172step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13173Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13173step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13173step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13173step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw13174step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13174step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw13174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw13175step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw13175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw13176step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw13176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw13177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13178step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13178step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw13179step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw13179step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13179step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw13179step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw13180step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13180step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw13181step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13181step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13182step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13182step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw13183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw13183step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13183step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw13184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw13184step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13184step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13184step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw13185step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13185step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13185step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13185step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13185step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw13186step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13186step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13186step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw13187step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13187step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1]]
def raw13188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw13188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw13188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13188step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13188step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13188step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13189Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13190Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13192Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw13194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13195 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![0, 0], ![1, -1]]
def raw13195Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13195step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]
def raw13195step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13195step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw13195step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13196step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13197step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw13198step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw13199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13203step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw13206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw13207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13211step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13211step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13212step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13213step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13213step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13213step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13214step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13215step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13215step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13215step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13216step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13217step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13218step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13218step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13218step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13219step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13219step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13220step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13220step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13221step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13221step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13222step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13223step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13224step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13225step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13225step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13226step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13226step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13227step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13227step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw13228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13228step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13228step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13228step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13229step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13229step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13230step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13231step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13231step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13232step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13232step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0]]
def raw13233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw13233step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13233step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw13233step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13234step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13234step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13234step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13235step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13235step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13236step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13237step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13237step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13237step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw13238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw13238step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw13238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13239step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13240step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13241step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13242step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13243step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13244Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13244step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13245Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13245step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13246Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13246step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13247Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13247step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13248step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13249step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13250step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13251step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13252step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13253step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13253step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13254step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13256step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw13258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13259Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13260step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13262step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0]]
def raw13263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw13263step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13264step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13266step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13267Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw13268Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw13268step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13269Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13269step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13269step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13269step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13270Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13270step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13270step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13271Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13271step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13271step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13271step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13272Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13272step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13272step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13273Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13273step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13273step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13274Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13274step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13274step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13274step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13275Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13275step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13275step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13275step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13275step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13276Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13276step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13276step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13276step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13276step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13277Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13277step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13277step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13277step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13278Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13278step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw13278step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13278step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13278step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13278step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13279Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13279step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13279step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13279step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13279step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13280Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13280step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13280step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13280step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13280step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13280step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13281Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13281step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13281step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13281step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13281step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13281step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13282Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13282step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13282step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13282step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13283Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13283step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw13283step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13283step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13283step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13283step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13284Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13284step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13284step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13284step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13284step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13285Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw13285step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13285step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw13285step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13285step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw13285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13286Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw13286step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw13286step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13286step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw13286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13287Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13287step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13287step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13287step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13287step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13287step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw13288step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw13288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw13288step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13288step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw13288step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13289Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13289step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13289step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13289step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13289step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13290step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13290step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13290step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13291step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13291step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13291step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13291step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13291step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13292step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13292step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13292step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13292step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0]]
def raw13293Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13293step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw13293step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13293step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13293step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw13294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13294step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13294step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw13295step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13295step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13295step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw13296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13296step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13296step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw13297step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13297step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13297step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13297step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw13298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13298step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw13298step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13298step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13298step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13299Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13299step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13300Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13300step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13301Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13301step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13302Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13302step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13302step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13302step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13303Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw13303step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13304Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13304step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13304step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13305 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![0, 0]]
def raw13305Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13305step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw13305step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13305step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw13305step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13305step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw13305step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13306Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13306step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13307Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13307step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13309step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw13312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13313step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13322 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13322step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13327 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13327step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13327step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13331 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13331step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13331step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13332 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13332Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13332step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13333 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13333Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13334 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw13334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw13334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13335 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13336 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13337 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13338 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw13338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13339 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw13339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw13339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13340 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13341 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13341Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13342 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13342Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13342step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13343 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw13343Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13344 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13344Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13344step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13345 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13345Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13346 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13346Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13346step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13347 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13347Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw13347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13348 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13348Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13352 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13352Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13352step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13352step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13357 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13357Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13357step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13357step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13358 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13358Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13358step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13358step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13358step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13358step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13359 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw13359Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13359step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13359step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13363 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13363Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13363step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13363step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13364 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13364step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13365 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw13365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13366 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw13366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw13366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13366step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw13366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13367 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13368 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw13368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13369 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13370 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw13370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13371 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13372 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13373 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13374 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw13374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw13374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13376step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13377step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw13378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13378step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw13379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13380step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13380step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13382step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw13383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13383step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw13384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13385step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13385step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13385step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13387step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw13388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw13389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13389step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13390step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13390step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13391step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw13393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw13393step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13393step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw13394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw13394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw13395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13395step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw13396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13396step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw13397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13397step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw13398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw13398step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13398step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw13399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13399step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13400step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13400step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13402step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13403step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw13404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13404step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13407step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw13408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw13409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13409step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13412step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw13413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13413step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw13414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13414step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13417step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw13418Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13418step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw13419Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13419step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13420Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13421Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13422Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw13423Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw13423step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw13424Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw13424step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13424step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw13425Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw13426Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw13427Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw13428Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw13428step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw13429Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13429step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13429step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13430Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13431Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13432Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13433Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13433step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13433step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw13434Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13434step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13435 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13435step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13435step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13435step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13436 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13436step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13436step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13437 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13437step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13437step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13438 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw13438step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13438step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13438step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13438step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13439 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13439step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13439step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw13440 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13440step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13440step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13441 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13441step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13441step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13441step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13442 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13442step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13442step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13442step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13442step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13443 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13443step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13443step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13443step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13444 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13444step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13444step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13445 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13445step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13445step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13445step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13446 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13446step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13446step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13446step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13446step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13447 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13447step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13447step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13447step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13448 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13448step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13448step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13449 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13449step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13449step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13450 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13450step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13450step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13451 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13451Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13451step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13451step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13452 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13452step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13453 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13453Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13453step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13453step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13454 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13454step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13454step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13455 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13455Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13455step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13455step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13456 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13456Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13456step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13456step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13456step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13456step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13457 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13457Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13457step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13457step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13457step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13457step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13458 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13458Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13458step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13459 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13459Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13459step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13460 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13460Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13460step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13460step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13460step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13461 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13461Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13461step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13461step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13461step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13462 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13462Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13462step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13464step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13465step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13465step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13465step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13465step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13466step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13466step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13466step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13466step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13466step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13467step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13467step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13467step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13467step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13467step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13468step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13470step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13473step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13473step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13478step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13478step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13478step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw13481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13483step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13483step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13483step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13484step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw13486step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw13487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw13487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13487step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13488step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw13488step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw13488step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13490step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13491step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw13491step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13491step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw13492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw13492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13492step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw13492step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13492step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13508step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13512step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13513step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13514step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13516step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw13517Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw13517step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13518Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13518step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw13518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13519Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13519step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw13519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13520Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw13520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13521Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13521step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw13522Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw13522step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13523step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13523step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13523step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13523step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13523step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13523step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13524step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13524step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13524step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13525Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13525step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13525step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13525step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13525step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13525step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13526step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13526step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13526step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13526step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13526step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13527Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13527step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13527step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13527step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13527step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13527step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13527step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13528step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13528step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13528step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13528step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13529Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13529step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13529step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13529step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13530step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13530step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13530step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13530step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13530step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13531Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13531step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13531step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13531step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13531step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13531step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13532Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13532step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13532step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13532step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13532step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13532step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13533Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13533step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13533step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13533step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13533step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13534Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13534step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13534step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13534step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13535Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13535step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13535step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13535step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13536Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13536step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13536step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13536step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13537Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13537step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13537step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13537step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13538Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13538step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw13538step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13538step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13538step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13538step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13538step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13539Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13539step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw13539step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13539step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13539step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13539step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13540Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13540step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13540step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13540step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13541Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13541step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw13541step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13541step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13541step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13541step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13542Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13542step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13542step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13542step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13542step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13542step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13543Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13543step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw13543step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13543step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13543step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13543step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13544Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13544step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw13544step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13544step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13544step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13544step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13545Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13545step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13545step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13545step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13546Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13546step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw13546step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13546step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13546step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13546step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw13547Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw13547step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13547step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13547step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13547step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13547step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13547step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13548Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13548step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw13548step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13548step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw13548step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13549Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13549step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw13549step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13549step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw13549step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13550Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw13550step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13550step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw13550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13551Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13551step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13551step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13551step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw13552Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw13552step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13552step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13552step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13553step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13559 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![1, -1], ![-1, 1]]
def raw13559Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13559step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]
def raw13559step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13559step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw13559step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13563step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13563step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13565step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw13568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13568step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13569step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13574step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13575step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13575step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw13576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13576step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13576step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13576step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13576step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13576step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13577step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13577step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13578step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13578step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13578step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13579step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw13580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13580step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13580step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13581step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13582step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13582step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13582step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13583step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13583step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13583step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13584step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw13585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13585step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw13585step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13585step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw13585step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13586step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13586step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13587step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13587step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13587step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13588step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13588step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13589step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw13590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw13590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13590step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13590step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13591step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13591step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13592step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13592step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13593step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw13594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13594step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13594step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13594step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13594step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13594step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13595step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13595step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13595step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13596step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw13598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13598step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13598step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13599step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13599step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13601step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw13602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13602step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13603Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13603step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13604Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13604step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13605Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13605step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13605step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13606Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13606step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw13607Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13607step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13607step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw13607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13608Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13608step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13609Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13609step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13610Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13610step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13610step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13611Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw13612Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw13612step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13613Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13613step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13614step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13615Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw13616Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13616step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13616step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13617 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13617step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13617step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13617step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13618 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13618step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13618step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13619 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13619step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13619step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13620 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13620step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13620step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13621 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13621step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13622 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13622step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13622step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13622step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13623 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13623step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13623step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13624 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13624step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13624step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13625 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13625step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13625step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13626 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw13626step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw13626step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13627 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13627step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13627step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13627step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13627step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13628 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13628step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13628step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13628step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13629 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw13629step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw13629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13630 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13630step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13630step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13630step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13630step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13631 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13631step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13631step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13631step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13631step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13632 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13632step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13633 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13633step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13633step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13634 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13634step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13634step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13635 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13635step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13635step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13635step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13635step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13636 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13636step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13636step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13636step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13636step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13637 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13637step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13637step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13637step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13638 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13638step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13638step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13638step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13639 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw13639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw13639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13639step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13639step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13640 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13640step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13640step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13640step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13640step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13640step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13641 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13641step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13641step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13641step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13642 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13642step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13642step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13642step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13643 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13643step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13643step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13644 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13645 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13646 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13647 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13649 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13650 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13651 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13652 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw13652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13654 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13654step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13656 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13656step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13657 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw13657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13658 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13658step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13658step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13659 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13659step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13659step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13659step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13660 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13660step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13661 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13662 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13663 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13663step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13664 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13664step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13665 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13665step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13666 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13666step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw13667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw13667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13668 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13668Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13668step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13668step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13669 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13669Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13669step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13669step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13670 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13670Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13670step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13671 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13671Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13671step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13672 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13672step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13673step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13673step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13673step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13673step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13675step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13675step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13675step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13675step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13676step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13676step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13676step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13676step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13677step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13677step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13677step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13677step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

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

def raw1247Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1247step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1247step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1247step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1247step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1248 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1248step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1249 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1249Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1249step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1250 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1250Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw1250step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1250step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1251 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1251step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1251step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1251step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1252 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1252Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1252step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1252step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1253 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1253Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1253step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw1253step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1253step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1253step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1253step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1253step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1254 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1254step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1255 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1255Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1256 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1256Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw1256step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1256step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1256step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1257 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1257step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1257step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1258 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1258Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1258step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1259 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1259Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw1259step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw1259step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1259step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw1259step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1260 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1260step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1261 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1261Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1262 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1262Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw1262step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1262step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1263 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1263step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1263step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1264 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1264Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1264step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1264step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1265 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1265Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1265step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw1265step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1265step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw1265step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1265step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw1265step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1266 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1266step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1266step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1267 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1268 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1268Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw1268step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1268step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1268step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1269 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1269step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1269step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1269step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1269step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1270 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1270Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1270step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1270step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1271 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1271Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1271step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw1271step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw1271step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1271step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw1271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1272 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1272step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1272step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1272step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1272step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1273 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1273Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1273step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1273step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1274 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1274Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1274step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw1274step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1274step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw1274step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1274step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw1274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1275 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1275step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1275step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1276 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1276Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1276step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1276step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1277 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1277Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1277step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw1277step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw1277step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1277step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw1277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1278 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 4, -2]]
def raw1278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1278step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw1278step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1278step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw1278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1279 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 4, -2]]
def raw1279Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1279step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw1279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw12478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12479 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12479Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12479step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw12479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12480 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12480step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12481 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12481step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12482 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12482step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12482step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12483 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12484 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw12484step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12485 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12486 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12486step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12487 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw12487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12488 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw12488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12489 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12490 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12490step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12490step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12490step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12491 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12491step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw12491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12492 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12493 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw12493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12494 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12494step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12494step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw12494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12495 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw12495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12496 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw12496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12503 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12503Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12503step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12503step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12513 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12514 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw12514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12515 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12515step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12516 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw12516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12517 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12517step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12517step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12518 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw12518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12519 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw12519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12520 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw12520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12521 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw12521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw12521step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12522 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw12522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12523 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![1, -2, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw12523step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12523step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw12523step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12524 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw12524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12525 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw12525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12526 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12527 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12527step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12527step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12527step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12528 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw12528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12528step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12529 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12530 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw12530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12533step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12533step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw12534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12534step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12535step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw12535step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12536step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12536step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12537step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12538step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12538step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw12539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12539step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12539step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12540step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12541step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12543step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12543step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw12544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw12544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12544step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12544step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12545step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12545step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12546step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12546step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12546step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12548step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw12549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw12549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw12549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12549step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12551step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12551step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12551step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12551step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12552step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12553step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12553step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw12554step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw12554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12554step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12554step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw12555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw12555step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12555step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12556step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12556step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12556step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12556step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw12560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12562Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12562step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12563Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12563step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12563step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12563step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw12564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12564step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12564step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12564step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12565step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12565step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12566Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12567Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12568Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12568step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw12569Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12569step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12569step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12571step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12573step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12573step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12573step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw12574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12574step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12574step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12574step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12574step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12575step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12578step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw12579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw12579step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw12579step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12579step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12580step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12580step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12582step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12583step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12583step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw12584step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw12584step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12584step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw12585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw12585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12589step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12589step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw12590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12590step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12591step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12591step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12591step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12593step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12594step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw12595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12595step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12596step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12596step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12596step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12597step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12597step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12598step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12599step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12599step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12599step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw12600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12600step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12600step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12600step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12600step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12601step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12601step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12601step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12602step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12602step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12603step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12603step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12604step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12604step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw12605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12605step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12605step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12605step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12605step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12606step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12607step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12608step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12608step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12609step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12609step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw12610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw12610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw12610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12610step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12610step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12610step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12610step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12611step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12611step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12612step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12612step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12613step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12613step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12614step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12614step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw12615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12615step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12615step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12615step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12615step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12615step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12616step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12616step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12617step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12617step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12618step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12618step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12619step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12619step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12620step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12620step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12621Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12621step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12622step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12623step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12624step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw12625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12625step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12625step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12625step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12625step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw12625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12626step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12627step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw12630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12630step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12631step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12632step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw12635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12635step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12637step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw12640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw12640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw12640step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12644step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw12645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12645step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12645step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12647step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12651 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12651step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12651step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12652 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12652step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12652step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw12653step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12653step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12653step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12654 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12654step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12655step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12656 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw12656step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12656step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12656step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12656step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12657 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12657step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12657step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12658 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12658step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12658step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12659 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw12659step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12659step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12659step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12659step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12659step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12660 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12660step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12661 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12661Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12661step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw12661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12662 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12662Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12662step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12662step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12663 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12663step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12664 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12664Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12664step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw12664step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12664step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12664step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12665 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12665Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12665step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw12665step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12665step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12666 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12666Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw12666step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12667Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw12667step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12667step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw12667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw12698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12700step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12701step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12701step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12701step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12702Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12702step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12704step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12706step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12706step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12707step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12707step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12708step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12708step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12709step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12710step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12710step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12711step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12711step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12711step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12712step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12713step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw12713step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw12714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12715step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw12715step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw12716step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12716step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw12716step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12716step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw12716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12717step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12717step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12718Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12718step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw12718step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12719Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw12719step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12720Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12720step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw12720step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12721Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12721step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12721step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw12722Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw12722step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw12722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12723Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12723step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12724Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12725Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12725step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12725step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12726Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12726step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12726step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1]]
def raw12727Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12727step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12727step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw12727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12728step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12728step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12729step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12729step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12730step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12731step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12731step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12731step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12731step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12731step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12731step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw12732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12732step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12733step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12733step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12734step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12735step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12735step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12735step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12736step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12736step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12736step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12736step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12736step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw12737step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12737step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12738step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12738step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12738step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12739step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12739step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12739step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12739step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12740step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12740step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12740step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12741step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12741step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12741step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12741step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12741step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12741step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12741step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12741step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12742step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12742step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12743step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw12743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw12743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw12744step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12744step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw12744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw12745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw12745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw12746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw12746step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12746step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw12746step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12746step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw12746step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw12747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw12747step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw12748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw12748step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12748step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw12748step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw12749step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12749step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12749step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12750step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw12750step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw12750step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12750step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw12750step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12751step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw12751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12751step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12751step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12751step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw12752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw12752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw12752step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12752step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12752step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12752step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12753step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw12753step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12753step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12753step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12753step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12754Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw12754step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12754step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12754step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12755Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12755step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw12755step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12755step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12755step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12755step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12755step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12756step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw12756step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12756step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12756step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12756step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1]]
def raw12757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12757step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12757step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw12757step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12757step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12757step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12757step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12757step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw12761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw12762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12764 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![-1, 1], ![0, 0], ![1, -1]]
def raw12764Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12764step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![-1, 1], ![1, -1]]
def raw12764step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12764step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-1, 1], ![1, -1]]
def raw12764step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12764step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw12764step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12765step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12765step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12766step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12766step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12766step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12766step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12767step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12767step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12768step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12768step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12769step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12769step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12769step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12769step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12769step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12769step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12769step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12770step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12771step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12771step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12772step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12773step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12774step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12775step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12776step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12777step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12777step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12778step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12778step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12778step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12779step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12779step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12779step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12779step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12780step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12780step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12781step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12781step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12782step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12782step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12783step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12783step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw12784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw12784step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12784step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12784step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12784step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12784step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12785step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12785step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12786step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12786step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12787step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12787step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw12788step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw12788step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0]]
def raw12789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw12789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw12789step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12789step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12789step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12789step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12789step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12790step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12790step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12790step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12791step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12792step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12792step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw12793step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw12793step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw12794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw12794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw12794step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12794step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw12794step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12796Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12796step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12797Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12797step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12797step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12798Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12798step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12799Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12799step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12799step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12799step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12799step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12799step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12799step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


