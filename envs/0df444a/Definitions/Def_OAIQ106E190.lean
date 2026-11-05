-- Prove2me | Definitions.Def_OAIQ106E190
-- name    : OAIQ106E190
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:33:41.377404+00:00
-- url     : https://prove2.me/theorems/e32a09c7-65d3-4353-8b97-c107b566707f
-- title:
--   Definitions bundle OAIQ106E190 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2793 declarations of OpenAI's Lean: 2793 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw22474step3`, `OAI.MUB6.Certificate.MixedSemantics.raw22474step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22475`, `OAI.MUB6.Certificate.MixedSemantics.raw22475Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22475step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22475step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22475step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22475step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22475step2`, `OAI.MUB6.Certificate.MixedSemantics.raw22475step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22475step3`, `OAI.MUB6.Certificate.MixedSemantics.raw22475step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22476`, `OAI.MUB6.Certificate.MixedSemantics.raw22476Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22476step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22476step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22476step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22476step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22476step2`, `OAI.MUB6.Certificate.MixedSemantics.raw22476step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22477`, `OAI.MUB6.Certificate.MixedSemantics.raw22477Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22477step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22477step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22477step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22477step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22477step2`, `OAI.MUB6.Certificate.MixedSemantics.raw22477step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22478`, `OAI.MUB6.Certificate.MixedSemantics.raw22478Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22478step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22478step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22478step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22478step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22478step2`, `OAI.MUB6.Certificate.MixedSemantics.raw22478step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22478step3`, `OAI.MUB6.Certificate.MixedSemantics.raw22478step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22479`, `OAI.MUB6.Certificate.MixedSemantics.raw22479Labels` and 2753 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical17`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical17.lean), [`MutuallyUnbiased_MixedSemantics_Canonical175`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical175.lean), [`MutuallyUnbiased_MixedSemantics_Canonical176`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical176.lean), [`MutuallyUnbiased_MixedSemantics_Canonical177`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical177.lean), [`MutuallyUnbiased_MixedSemantics_Canonical178`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical178.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound2574_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2576_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound38_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound39_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound42_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound45_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound79_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound98_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1436_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2063_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound744_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.originalReductionEval_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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
def raw226Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw226step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw227 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw227Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw227step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

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
def raw2267Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw2267step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2267step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2267step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2268 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2268step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2268step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2268step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2269 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2270 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2270Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw2270step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2270step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2270step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2270step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2271 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2271step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2272 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2272step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2273 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2273Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw2273step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2273step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2274 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2274step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2275 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2276 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2276Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw2276step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2276step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2276step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2277 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 3, -2]]
def raw2277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2277step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw2277step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw2277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2278 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 3, -2]]
def raw2278Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2278step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw2278step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2279 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 3, -2]]
def raw2279Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2279step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw2279step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2279step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw2279step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2280 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2280step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2281 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2281Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2281step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2282 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2282Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2282step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2282step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2282step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2283 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 2, -3]]
def raw2283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2283step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw2283step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw2283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2284 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 2, -3]]

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
def raw22672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22672step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw22672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22673step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22673step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22673step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22674step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22675step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22677Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22677step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22677step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw22677step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22678step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22680step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22681step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22684step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22685step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22685step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22686step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22689step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22689step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22689step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22689step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22690step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22690step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22693step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22693step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw22693step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22694step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw22694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22695step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22696step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22698step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw22698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22699Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22699step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22699step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw22699step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22699step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22699step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22699step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22699step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22700Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22700step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw22700step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22700step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22700step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22700step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22701Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw22701step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22701step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22702step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw22702step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw22702step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22702step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw22702step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22703step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw22703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22703step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22703step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22703step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22704step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw22704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22704step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22704step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22704step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw22705step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22705step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22705step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw22706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw22706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22706step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw22706step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw22707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22707step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22708step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22708step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw22708step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22708step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22708step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22708step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22708step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22709step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw22709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22709step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22709step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22709step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw22710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22711step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22711step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw22711step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22711step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22711step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22711step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22711step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22712step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw22712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22712step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22712step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22712step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22712step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22713step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw22713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22713step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22713step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22713step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22714step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw22714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22714step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22714step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22715step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw22715step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22715step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw22715step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22715step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw22715step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22716step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22716step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22716step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22716step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22716step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22716step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22716step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22716step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22717step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22717step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22717step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw22717step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22717step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22717step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22717step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22717step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw22718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22718step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw22719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22719step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22719step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22719step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22720step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22720step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw22720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22720step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw22720step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22720step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw22720step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22721Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22721step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22721step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22722Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22722step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22723Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22723step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22724step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22725Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22725step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22727step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22728Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22728step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22730step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22731Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22731step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22731step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22737step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22737step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22737step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22738step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22738step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22739step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22739step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22740step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22740step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22740step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22741step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22741step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22741step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22742step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22742step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22743step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22743step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22743step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22744step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22744step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22745step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22745step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22745step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22745step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22746step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22746step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22746step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22747step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22747step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22748step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22748step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22748step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22748step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22749step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22749step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22749step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22750step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22750step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22751step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22751step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw22752step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22752step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw22752step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22753step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw22753step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22753step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw22753step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22754Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22754step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22755Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22756Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22756step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22757Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22757step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22758Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22758step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22759Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22760Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22760step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22761Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22761step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22762Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22762step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22762step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22763Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22763step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22764Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22764step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22765Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22765step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22765step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22765step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22766Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22766step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22766step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22766step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22767Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22767step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22768Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22768step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22769Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22769step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22769step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22769step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw22769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22770step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22770step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22770step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw22770step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22775 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22775step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22779 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22779step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22783 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22783step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22783step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22783step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22783step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22783step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical178
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22788 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22788step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22788step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22788step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22788step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22788step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22796 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22796Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22796step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22818 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22818step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22818step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22818step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22821 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22821Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22821step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22821step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22821step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22828 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22828Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22828step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22828step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22828step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22828step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-1, -1, 2]]
def raw22828step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22828step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def raw22828step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22828step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def raw22828step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22831 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22831Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22831step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22831step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22831step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, -1, 2], ![-1, -1, 2]]
def raw22831step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22831step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw22831step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22831step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw22831step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


