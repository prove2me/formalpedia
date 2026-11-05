-- Prove2me | Definitions.Def_OAIQ106E195
-- name    : OAIQ106E195
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:35:13.090576+00:00
-- url     : https://prove2.me/theorems/0fa61248-0e13-415a-9a6f-a2e5b97b4fec
-- title:
--   Definitions bundle OAIQ106E195 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1994 declarations of OpenAI's Lean: 1994 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw25186`, `OAI.MUB6.Certificate.MixedSemantics.raw25186Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25186step0`, `OAI.MUB6.Certificate.MixedSemantics.raw25186step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25186step1`, `OAI.MUB6.Certificate.MixedSemantics.raw25186step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25187`, `OAI.MUB6.Certificate.MixedSemantics.raw25187Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25187step0`, `OAI.MUB6.Certificate.MixedSemantics.raw25187step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25188`, `OAI.MUB6.Certificate.MixedSemantics.raw25188Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25188step0`, `OAI.MUB6.Certificate.MixedSemantics.raw25188step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25188step1`, `OAI.MUB6.Certificate.MixedSemantics.raw25188step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25189`, `OAI.MUB6.Certificate.MixedSemantics.raw25189Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25189step0`, `OAI.MUB6.Certificate.MixedSemantics.raw25189step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25189step1`, `OAI.MUB6.Certificate.MixedSemantics.raw25189step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2518Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2518step0`, `OAI.MUB6.Certificate.MixedSemantics.raw2518step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2519`, `OAI.MUB6.Certificate.MixedSemantics.raw25190`, `OAI.MUB6.Certificate.MixedSemantics.raw25190Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25190step0`, `OAI.MUB6.Certificate.MixedSemantics.raw25190step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25190step1`, `OAI.MUB6.Certificate.MixedSemantics.raw25190step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25191`, `OAI.MUB6.Certificate.MixedSemantics.raw25191Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25191step0`, `OAI.MUB6.Certificate.MixedSemantics.raw25191step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25191step1`, `OAI.MUB6.Certificate.MixedSemantics.raw25191step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25192`, `OAI.MUB6.Certificate.MixedSemantics.raw25192Labels` and 1954 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical19`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical19.lean), [`MutuallyUnbiased_MixedSemantics_Canonical196`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical196.lean), [`MutuallyUnbiased_MixedSemantics_Canonical197`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical197.lean), [`MutuallyUnbiased_MixedSemantics_Canonical198`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical198.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound2636_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5433_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5434_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5435_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5439_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound101_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound40_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound43_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound45_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1472_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1479_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound612_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound957_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound974_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1912_e`.
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

def raw252 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw252Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw252step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw253 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw253Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw253step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw254 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]

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

def raw2518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2519 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw2519Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2519step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2520 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2520step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2520step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2521 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2522 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2522Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw2522step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2522step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2522step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2523 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2523step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2524 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2525 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2525Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2525step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2526 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2526step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2527 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2528 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2528Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2528step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2528step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2528step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2529 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2529step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2529step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2530 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2531 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2531Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw2531step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2531step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2532 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2532step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2532step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2533 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2534 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2534Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw2534step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw2534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2535 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2535step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2535step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2536 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2537 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2537Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2537step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2537step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2537step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2538 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2538step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2538step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2539 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2540 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2540Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2540step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw2540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw2540step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2541 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2541step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2541step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2542 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2543 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2543Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw2543step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2543step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2544 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0]]
def raw2544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2544step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2544step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2545 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0]]
def raw2545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2545step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2546 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical196
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25186Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25186step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25187Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25187step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25188Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25188step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw25188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25189Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25189step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25189step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25190Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25190step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25191Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25191step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25192Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25193Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25193step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw25193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw25194Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25194step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25194step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25194step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25194step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw25194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25195step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25195step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25195step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25195step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25196step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25197step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw25197step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25197step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25197step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25197step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25198step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25198step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25198step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25198step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25198step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25198step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25198step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25198step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25198step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25199step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25199step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25199step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25199step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25200step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25200step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25200step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25200step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25201step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25201step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25201step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25201step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25202step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25202step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25203step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25203step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25203step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25203step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25203step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25203step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25203step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25203step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25203step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25204step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25204step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25204step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25205step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25205step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25205step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25205step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25205step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25206step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25206step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25206step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25206step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw25207step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25207step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25207step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25207step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25208step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25208step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25208step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25209step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25209step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25209step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25209step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25210step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw25210step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25210step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25210step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25210step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25211step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw25211step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw25211step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25211step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw25211step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw25212step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25212step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25212step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25213Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25213step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25213step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw25213step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25213step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25213step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25213step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25214step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25214step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25214step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25214step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25214step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25215Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25215step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25215step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25215step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25215step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25215step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical197
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25216Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25216step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25216step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25216step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25216step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25216step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25217Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25217step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25217step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25217step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25217step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25218Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25218step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw25218step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25218step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25218step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25218step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25219Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25219step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25219step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25219step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25219step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25219step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25220step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw25220step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25220step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25220step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25220step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25221Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25221step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw25221step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25221step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw25221step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25221step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw25221step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw25222step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25222step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25222step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25222step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25223Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25223step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw25223step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25223step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25223step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25223step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw25224Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25224step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25224step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25224step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw25224step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25224step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25224step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25224step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25224step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25225step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25228step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25231 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![0, 0], ![1, -1]]
def raw25231Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25231step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw25231step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25231step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw25231step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25232Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25232step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25233step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25233step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25234Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25234step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25234step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25235Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25235step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25235step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25236Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25236step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25236step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25237Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25237step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25238Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25238step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25239Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25239step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25240Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25240step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25241step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25241step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25242step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25242step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25242step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25243step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25243step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25244step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25244step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25245step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25245step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25246step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25246step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25247step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25248step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25249step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25250step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25251step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25252step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25253step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25253step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25254step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25255step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25262step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25263step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25264step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25271step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25272 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25272step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25272step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25273 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw25273step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25273step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25273step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25273step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25274 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25274step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25275 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25275step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25275step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25276 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25276step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25276step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25277 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25277step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25278 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25278step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25279 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25279step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25280 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25280step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25280step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25281 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw25281step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25281step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25281step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25281step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25281step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25282 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25282step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25282step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25282step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25283 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25283step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25283step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25284 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25284step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25284step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25284step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25285 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25285step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25286 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25286step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25286step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25286step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25286step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25286step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25287 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25287step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25287step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25288 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25288step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25289 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25289step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25289step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25290 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25290Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25290step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25290step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25291 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25291Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25291step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25292 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25292Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25292step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25292step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25293 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25293Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25293step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25293step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25294 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25294step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25295 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25295step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25296 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25296step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25297 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25297step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25298 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25298step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25299 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25299step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25300 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25300step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25301 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25302 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25303 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25303step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25304 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25304step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25304step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25305 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25306 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25307 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25308 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25308step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25309 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25309Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25309step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25309step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25310 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25310step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25310step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25311 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25311step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25311step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25312 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25312step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25313 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25313step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25314 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25314step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25314step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25315 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25315Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25315step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25315step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25315step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25316 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25316step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25317 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25317step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25317step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25317step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25318 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25319 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25319step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25320 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25320step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25321 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25321Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25321step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25321step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25321step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25321step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25321step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25321step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25322 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25322step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25322step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25322step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25322step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25322step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25323 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25323Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25323step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25324 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25324step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25325 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25325Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25325step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25325step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25326 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25326step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25326step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25327 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25327Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25327step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25327step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25327step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25327step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25327step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25327step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25328 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25328step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25329 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25329Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25329step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25329step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25330 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25330step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25330step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25331 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25331Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25331step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw25331step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25331step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25331step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25331step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25332 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25332step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25333 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25333Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25333step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25333step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw25338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw25338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw25339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw25339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25340 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![-1, 1], ![2, -2]]
def raw25340Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25340step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![-1, 1], ![2, -2]]
def raw25340step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25340step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw25340step1Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical198
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25346 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25346step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25346step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25347 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw25347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25347step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25347step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25348 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25349 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw25349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25350 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25351 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw25351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25351step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25351step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25352step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25354step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25360step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25361step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25361step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25363step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25364step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25364step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25366step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25367step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25368step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25368step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25371step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25371step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw25371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25375step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25381step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25384step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25384step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25385step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25388step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25389Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25389step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25389step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw25390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw25390step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25390step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25390step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25391Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25391step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw25391step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25391step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25391step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25391step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25392Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw25392step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25392step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25392step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25392step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25393Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25393step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25393step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25393step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw25393step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25393step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25393step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25393step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25393step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25394Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25394step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw25394step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25394step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25394step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25394step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25395Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25395step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25395step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25395step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25395step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25395step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25396Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25396step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25396step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25396step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25397Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25397step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25397step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25397step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25397step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25397step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25397step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25397step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25398Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25398step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25398step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25398step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25398step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25398step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25398step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25399Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw25399step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25399step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25399step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25400Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw25400step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25400step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25400step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25401Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25401step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw25401step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25401step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25401step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25401step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25402Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw25402step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25402step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25402step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25402step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25403Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25403step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25403step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25403step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25403step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25403step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25403step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25404step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw25404step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25404step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25404step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25404step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25405Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25405step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25405step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25405step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25405step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25405step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25406step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25406step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25406step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25406step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25406step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25406step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25406step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25407Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25407step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw25407step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25407step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25407step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25407step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25408step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25408step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25408step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25408step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25408step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25409Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25409step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw25409step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25409step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25409step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25409step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25410step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25410step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25410step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25411Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25411step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw25411step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25411step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25411step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25411step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25411step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw25412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw25412step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25412step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25412step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25412step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw25412step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25412step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw25412step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25412step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw25412step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25427step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25427step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25428step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25428step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25429step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25430step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25430step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25431step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25431step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25432step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25433step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25434step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25434step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25435step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25435step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25436step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25436step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25437step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25437step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25438step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25438step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25439step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25439step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25440step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25440step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25440step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25441step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25441step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25442step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25442step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25443step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25443step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25444step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25444step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25444step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25445step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25445step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25445step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25446step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25446step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25446step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25447step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25447step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25448step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw25448step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw25448step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25449Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25449step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25450Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25450step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25451Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25452Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25452step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25453Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25453step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25454Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25455Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25456Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25457Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25458Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25458step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25459Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25459step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25460Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25461Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25461step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25461step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25462Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25462step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25463Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25463step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25464Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25464step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25464step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25465Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


