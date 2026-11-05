-- Prove2me | Definitions.Def_OAIQ106E100
-- name    : OAIQ106E100
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:09:41.090445+00:00
-- url     : https://prove2.me/theorems/569576e0-d46d-4316-9d75-f15092b8fa14
-- title:
--   Definitions bundle OAIQ106E100 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2680 declarations of OpenAI's Lean: 2680 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw2429Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2429step0`, `OAI.MUB6.Certificate.MixedSemantics.raw2429step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2429step1`, `OAI.MUB6.Certificate.MixedSemantics.raw2429step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2429step2`, `OAI.MUB6.Certificate.MixedSemantics.raw2429step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw242Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw242step0`, `OAI.MUB6.Certificate.MixedSemantics.raw242step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw242step1`, `OAI.MUB6.Certificate.MixedSemantics.raw242step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw243`, `OAI.MUB6.Certificate.MixedSemantics.raw2430`, `OAI.MUB6.Certificate.MixedSemantics.raw24300`, `OAI.MUB6.Certificate.MixedSemantics.raw24300Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24300step0`, `OAI.MUB6.Certificate.MixedSemantics.raw24300step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24300step1`, `OAI.MUB6.Certificate.MixedSemantics.raw24300step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24300step2`, `OAI.MUB6.Certificate.MixedSemantics.raw24300step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24301`, `OAI.MUB6.Certificate.MixedSemantics.raw24301Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24301step0`, `OAI.MUB6.Certificate.MixedSemantics.raw24301step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24301step1`, `OAI.MUB6.Certificate.MixedSemantics.raw24301step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24302`, `OAI.MUB6.Certificate.MixedSemantics.raw24302Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24302step0`, `OAI.MUB6.Certificate.MixedSemantics.raw24302step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24302step1`, `OAI.MUB6.Certificate.MixedSemantics.raw24302step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24303`, `OAI.MUB6.Certificate.MixedSemantics.raw24303Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24303step0`, `OAI.MUB6.Certificate.MixedSemantics.raw24303step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24303step1`, `OAI.MUB6.Certificate.MixedSemantics.raw24303step1Labels` and 2640 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical18.lean), [`MutuallyUnbiased_MixedSemantics_Canonical189`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical189.lean), [`MutuallyUnbiased_MixedSemantics_Canonical19`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical19.lean), [`MutuallyUnbiased_MixedSemantics_Canonical190`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical190.lean), [`MutuallyUnbiased_MixedSemantics_Canonical191`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical191.lean), [`MutuallyUnbiased_MixedSemantics_Canonical192`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical192.lean), [`MutuallyUnbiased_MixedSemantics_Canonical193`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical193.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound5174_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5386_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5387_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound47_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound50_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound53_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound89_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1434_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1436_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1479_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2063_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992_e`.
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical189
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

end MUB6.Certificate.MixedSemantics

end OAI
end


