-- Prove2me | Definitions.Def_OAIQ106E097
-- name    : OAIQ106E097
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:07:26.978934+00:00
-- url     : https://prove2.me/theorems/11277d33-fe6b-4087-bba4-b63238e66670
-- title:
--   Definitions bundle OAIQ106E097 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2769 declarations of OpenAI's Lean: 2769 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw20930Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20930step0`, `OAI.MUB6.Certificate.MixedSemantics.raw20930step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20930step1`, `OAI.MUB6.Certificate.MixedSemantics.raw20930step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20930step2`, `OAI.MUB6.Certificate.MixedSemantics.raw20930step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20931`, `OAI.MUB6.Certificate.MixedSemantics.raw20931Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20931step0`, `OAI.MUB6.Certificate.MixedSemantics.raw20931step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20931step1`, `OAI.MUB6.Certificate.MixedSemantics.raw20931step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20932`, `OAI.MUB6.Certificate.MixedSemantics.raw20932Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20932step0`, `OAI.MUB6.Certificate.MixedSemantics.raw20932step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20932step1`, `OAI.MUB6.Certificate.MixedSemantics.raw20932step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20932step2`, `OAI.MUB6.Certificate.MixedSemantics.raw20932step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20933`, `OAI.MUB6.Certificate.MixedSemantics.raw20933Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20933step0`, `OAI.MUB6.Certificate.MixedSemantics.raw20933step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20933step1`, `OAI.MUB6.Certificate.MixedSemantics.raw20933step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20933step2`, `OAI.MUB6.Certificate.MixedSemantics.raw20933step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20934`, `OAI.MUB6.Certificate.MixedSemantics.raw20934Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20934step0`, `OAI.MUB6.Certificate.MixedSemantics.raw20934step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20934step1`, `OAI.MUB6.Certificate.MixedSemantics.raw20934step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20935`, `OAI.MUB6.Certificate.MixedSemantics.raw20935Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20935step0`, `OAI.MUB6.Certificate.MixedSemantics.raw20935step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20935step1` and 2729 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical0.lean), [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical16.lean), [`MutuallyUnbiased_MixedSemantics_Canonical163`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical163.lean), [`MutuallyUnbiased_MixedSemantics_Canonical164`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical164.lean), [`MutuallyUnbiased_MixedSemantics_Canonical165`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical165.lean), [`MutuallyUnbiased_MixedSemantics_Canonical166`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical166.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1162_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2527_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2528_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2530_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound45_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound50_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound52_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound71_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound72_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound74_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound90_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound446_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978_e`.
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

end MUB6.Certificate.MixedSemantics

end OAI
end


