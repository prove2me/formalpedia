-- Prove2me | Definitions.Def_OAIQ106E188
-- name    : OAIQ106E188
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:33:14.543211+00:00
-- url     : https://prove2.me/theorems/f2010016-a9dd-410a-8412-1b02cb081cbf
-- title:
--   Definitions bundle OAIQ106E188 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2796 declarations of OpenAI's Lean: 2796 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw2135step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2136`, `OAI.MUB6.Certificate.MixedSemantics.raw21364`, `OAI.MUB6.Certificate.MixedSemantics.raw21364Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21364step0`, `OAI.MUB6.Certificate.MixedSemantics.raw21364step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21364step1`, `OAI.MUB6.Certificate.MixedSemantics.raw21364step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21364step2`, `OAI.MUB6.Certificate.MixedSemantics.raw21364step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21364step3`, `OAI.MUB6.Certificate.MixedSemantics.raw21364step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21365`, `OAI.MUB6.Certificate.MixedSemantics.raw21365Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21365step0`, `OAI.MUB6.Certificate.MixedSemantics.raw21365step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21365step1`, `OAI.MUB6.Certificate.MixedSemantics.raw21365step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21365step2`, `OAI.MUB6.Certificate.MixedSemantics.raw21365step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21366`, `OAI.MUB6.Certificate.MixedSemantics.raw21366Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21366step0`, `OAI.MUB6.Certificate.MixedSemantics.raw21366step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21366step1`, `OAI.MUB6.Certificate.MixedSemantics.raw21366step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21366step2`, `OAI.MUB6.Certificate.MixedSemantics.raw21366step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21367`, `OAI.MUB6.Certificate.MixedSemantics.raw21367Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21367step0`, `OAI.MUB6.Certificate.MixedSemantics.raw21367step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21367step1`, `OAI.MUB6.Certificate.MixedSemantics.raw21367step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21367step2`, `OAI.MUB6.Certificate.MixedSemantics.raw21367step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21367step3`, `OAI.MUB6.Certificate.MixedSemantics.raw21367step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21368`, `OAI.MUB6.Certificate.MixedSemantics.raw21368Labels` and 2756 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical16.lean), [`MutuallyUnbiased_MixedSemantics_Canonical166`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical166.lean), [`MutuallyUnbiased_MixedSemantics_Canonical167`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical167.lean), [`MutuallyUnbiased_MixedSemantics_Canonical168`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical168.lean), [`MutuallyUnbiased_MixedSemantics_Canonical169`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical169.lean), [`MutuallyUnbiased_MixedSemantics_Canonical17`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical17.lean), [`MutuallyUnbiased_MixedSemantics_Canonical170`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical170.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound2530_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound26_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound43_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound73_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound74_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound75_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound79_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1436_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound446_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound744_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990_e`.
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
def raw216Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw216step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw217 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

end MUB6.Certificate.MixedSemantics

end OAI
end


