-- Prove2me | Definitions.Def_OAIQ106E193
-- name    : OAIQ106E193
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:34:30.178292+00:00
-- url     : https://prove2.me/theorems/e6db1a67-9b6f-46a3-8e2e-75d97d8c273b
-- title:
--   Definitions bundle OAIQ106E193 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1986 declarations of OpenAI's Lean: 1986 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw24054step0`, `OAI.MUB6.Certificate.MixedSemantics.raw24054step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24055`, `OAI.MUB6.Certificate.MixedSemantics.raw24055Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24055step0`, `OAI.MUB6.Certificate.MixedSemantics.raw24055step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24056`, `OAI.MUB6.Certificate.MixedSemantics.raw24056Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24056step0`, `OAI.MUB6.Certificate.MixedSemantics.raw24056step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24057`, `OAI.MUB6.Certificate.MixedSemantics.raw24057Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24057step0`, `OAI.MUB6.Certificate.MixedSemantics.raw24057step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24058`, `OAI.MUB6.Certificate.MixedSemantics.raw24058Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24058step0`, `OAI.MUB6.Certificate.MixedSemantics.raw24058step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24059`, `OAI.MUB6.Certificate.MixedSemantics.raw24059Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24059step0`, `OAI.MUB6.Certificate.MixedSemantics.raw24059step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2405Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2405step0`, `OAI.MUB6.Certificate.MixedSemantics.raw2405step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2405step1`, `OAI.MUB6.Certificate.MixedSemantics.raw2405step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2405step2`, `OAI.MUB6.Certificate.MixedSemantics.raw2405step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2406`, `OAI.MUB6.Certificate.MixedSemantics.raw24060`, `OAI.MUB6.Certificate.MixedSemantics.raw24060Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24060step0`, `OAI.MUB6.Certificate.MixedSemantics.raw24060step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24061`, `OAI.MUB6.Certificate.MixedSemantics.raw24061Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24062`, `OAI.MUB6.Certificate.MixedSemantics.raw24062Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24062step0`, `OAI.MUB6.Certificate.MixedSemantics.raw24062step0Labels` and 1946 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical18.lean), [`MutuallyUnbiased_MixedSemantics_Canonical187`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical187.lean), [`MutuallyUnbiased_MixedSemantics_Canonical188`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical188.lean), [`MutuallyUnbiased_MixedSemantics_Canonical189`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical189.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound2599_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5174_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound50_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound52_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound87_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2063_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986_e`.
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

end MUB6.Certificate.MixedSemantics

end OAI
end


