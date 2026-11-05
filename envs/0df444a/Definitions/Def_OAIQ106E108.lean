-- Prove2me | Definitions.Def_OAIQ106E108
-- name    : OAIQ106E108
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:17:10.014311+00:00
-- url     : https://prove2.me/theorems/a2c4f66b-d983-402f-a783-7746a6f23615
-- title:
--   Definitions bundle OAIQ106E108 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7412 declarations of OpenAI's Lean: 7412 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw34253step1`, `OAI.MUB6.Certificate.MixedSemantics.raw34254`, `OAI.MUB6.Certificate.MixedSemantics.raw34254Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34254step0`, `OAI.MUB6.Certificate.MixedSemantics.raw34254step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34254step1`, `OAI.MUB6.Certificate.MixedSemantics.raw34254step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34254step2`, `OAI.MUB6.Certificate.MixedSemantics.raw34254step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34254step3`, `OAI.MUB6.Certificate.MixedSemantics.raw34254step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34255`, `OAI.MUB6.Certificate.MixedSemantics.raw34255Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34255step0`, `OAI.MUB6.Certificate.MixedSemantics.raw34255step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34255step1`, `OAI.MUB6.Certificate.MixedSemantics.raw34255step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34255step2`, `OAI.MUB6.Certificate.MixedSemantics.raw34255step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34256`, `OAI.MUB6.Certificate.MixedSemantics.raw34256Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34256step0`, `OAI.MUB6.Certificate.MixedSemantics.raw34256step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34256step1`, `OAI.MUB6.Certificate.MixedSemantics.raw34256step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34256step2`, `OAI.MUB6.Certificate.MixedSemantics.raw34256step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34257`, `OAI.MUB6.Certificate.MixedSemantics.raw34257Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34257step0`, `OAI.MUB6.Certificate.MixedSemantics.raw34257step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34257step1`, `OAI.MUB6.Certificate.MixedSemantics.raw34257step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34257step2`, `OAI.MUB6.Certificate.MixedSemantics.raw34257step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34258`, `OAI.MUB6.Certificate.MixedSemantics.raw34258Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34258step0`, `OAI.MUB6.Certificate.MixedSemantics.raw34258step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34258step1` and 7372 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical26`, `MutuallyUnbiased_MixedSemantics_Canonical267`, `MutuallyUnbiased_MixedSemantics_Canonical268`, `MutuallyUnbiased_MixedSemantics_Canonical269`, `MutuallyUnbiased_MixedSemantics_Canonical27`, `MutuallyUnbiased_MixedSemantics_Canonical270`, `MutuallyUnbiased_MixedSemantics_Canonical271`, `MutuallyUnbiased_MixedSemantics_Canonical272`, `MutuallyUnbiased_MixedSemantics_Canonical273`, `MutuallyUnbiased_MixedSemantics_Canonical274`, `MutuallyUnbiased_MixedSemantics_Canonical275`, `MutuallyUnbiased_MixedSemantics_Canonical276`, `MutuallyUnbiased_MixedSemantics_Canonical277`, `MutuallyUnbiased_MixedSemantics_Canonical278`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1170_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2996_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3003_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound65_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero488_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2063_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound37_e`.
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

def raw34Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw344 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw344Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw344step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw345 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw345Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw345step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw346 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw346Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw346step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw347 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw347Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw347step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw348 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw348Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw348step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw349 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw349Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw349step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw350 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw350Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw350step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw351 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw351Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw351step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw352 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw352Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw352step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw353 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw353Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw353step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw354 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw354Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw354step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw355 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw355Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw355step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw356 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 2, -3], ![-2, 2, 0]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]
def raw3425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3425step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3425step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3426step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3426step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3426step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3427step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3428step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3429step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3430step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3430step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3431 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3431Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3431step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3431step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3431step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3431step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3431step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3431step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3431step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3432 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3432Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3432step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3432step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3432step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3432step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3432step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3433 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3433Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3433step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3433step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3433step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3433step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3434 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3434Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3434step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3434step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3434step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![1, -1, 0]]
def raw3434step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3434step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -1, 0]]
def raw3434step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3434step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]
def raw3434step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3435 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0]]
def raw3435Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3435step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3435step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3435step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3435step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![1, -1, 0]]
def raw3435step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3435step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -1, 0]]
def raw3435step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3435step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]
def raw3435step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3436Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3436step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3436step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw3436step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3436step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3436step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3437Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3437step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3437step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3437step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3437step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3438Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3438step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3438step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3438step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3438step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3438step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0]]
def raw3439Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3439step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3439step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3439step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3439step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3440Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3440step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3440step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw3440step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3440step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3440step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3441Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3441step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3441step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3442Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3442step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3442step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3442step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3442step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3442step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw3443Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3443step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3443step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3443step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3443step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3444Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3444step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3444step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3444step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3444step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw3444step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3444step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw3444step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3445Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3445step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3445step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw3445step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3445step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw3445step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3445step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3445step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3446Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3446step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3446step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw3446step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3446step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw3446step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3446step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3446step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0]]
def raw3447Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3447step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3447step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3447step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3447step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw3447step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3447step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw3447step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3447step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw3447step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3447step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3447step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3448Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3448step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3448step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3448step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3448step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw3448step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3448step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw3448step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3449Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3449step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3449step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw3449step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3449step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw3449step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3449step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3449step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3450Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3450step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3450step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw3450step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3450step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw3450step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3450step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3450step3Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical267
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34253step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]

def raw34254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw34254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw34254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw34254step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw34254step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34254step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw34254step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34255step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34256step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34256step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34257step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34257step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34257step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34258step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw34259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw34259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34259step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34259step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34259step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw34260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw34260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34260step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34260step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw34261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw34261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34261step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw34262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34262step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw34263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw34263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw34263step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw34263step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw34264step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34264step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34264step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34264step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34264step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34265 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw34265step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34265step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34265step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34265step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34266 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw34266step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34266step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34266step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34266step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34267 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw34267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -3, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw34267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw34267step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw34267step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw34268step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34268step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34268step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34268step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34269 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw34269step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34269step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34269step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34269step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34270step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34270step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34270step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34270step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34271step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34271step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34271step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34271step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34272step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34272step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34272step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34272step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw34273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw34273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34273step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34273step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34273step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34273step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34274step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34274step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34274step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34274step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw34278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw34282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw34282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw34287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw34287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34292step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34292step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34292step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34292step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34293step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34293step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34293step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34293step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34293step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34294step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34294step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34294step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34294step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw34295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34295step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34295step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34295step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34295step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34295step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34295step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw34296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw34296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34296step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34296step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34296step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34296step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34297step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34298step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw34300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw34301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34302step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical268
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw34304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw34305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw34305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw34309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw34309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw34310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw34311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw34313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw34313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw34313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34314step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34314step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34314step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34314step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34315step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34315step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34316step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34316step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34316step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34316step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw34316step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34316step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw34316step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34317step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34317step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34321step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34322step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34323step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw34324step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw34327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw34327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw34327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34350Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34350step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34350step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34350step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34350step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34350step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34351Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34351step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34352Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34352step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34352step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34352step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw34352step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34352step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw34352step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34353Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34353step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw34353step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34353step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34353step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34353step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34354Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34354step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34354step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34354step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34354step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34355Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34355step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34355step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34355step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34355step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34355step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34355step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34356Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw34356step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34356step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34356step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34356step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34356step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34357Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34357step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw34357step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34357step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34357step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34357step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34358Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw34358step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34358step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34358step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34358step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34359Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34359step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34359step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34359step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw34359step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34359step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw34359step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34359step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw34359step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34360Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34360step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw34360step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34360step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw34360step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34360step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw34360step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34361Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34361step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw34361step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34361step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34361step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34361step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34361step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34362Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw34362step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34362step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34362step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw34363Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw34363step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw34363step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw34363step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34363step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw34363step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34373step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34373step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34373step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34373step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34374step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34374step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34374step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34374step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw34375step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34375step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34375step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34375step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw34376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw34376step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34376step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34376step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34376step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34377step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34377step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34377step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34377step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34378step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw34381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw34385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 1, -2]]
def raw34390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw34391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw34392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw34392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw34393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw34394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34395step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34395step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34395step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34395step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34396 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34396step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34396step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34396step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34396step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34397 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34397step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34397step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34397step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34397step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34397step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34398step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34398step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34398step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34398step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34399 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34399step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34399step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34399step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34399step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw34400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34400step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34400step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34400step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34400step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34401 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw34401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34401step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34401step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34401step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34401step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34402 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw34402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw34402step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34402step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34402step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34402step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34402step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34403 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw34403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw34403step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34403step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34403step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34403step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw34404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34404step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34404step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34404step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34404step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34404step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34405step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw34405step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw34406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34406step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34406step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34407step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34407step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![1, -1], ![2, -2]]
def raw34407step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34407step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw34407step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34408step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![2, -2]]
def raw34408step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34408step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw34408step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, -2, 0]]
def raw34409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw34409step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw34409step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34409step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw34409step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34416 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]
def raw34416Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34416step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw34416step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34416step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw34416step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical269
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34432step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34433step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34434step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34435step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw34438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34440step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34440step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34441step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34442step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34442step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34443step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34443step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34444step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34444step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34445step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34445step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34445step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34446step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34446step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34446step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34447step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34447step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34448step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34448step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34449step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34449step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34449step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34450step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34450step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34450step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34451step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34451step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34451step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34452step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34452step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34453step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34453step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34453step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34454step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34454step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34454step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34455step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34455step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34456step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34456step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34456step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34457step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34457step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34458step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34458step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34459step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34459step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34460step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34460step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw34461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34461step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34461step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34461step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34462step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34462step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34463step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw34464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34464step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34464step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34464step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34464step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34483step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34488step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34490step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34493step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34494step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw34495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34495step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw34497Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34497step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34498step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34498step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34498step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw34499step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34499step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34499step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw34500step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34500step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34500step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34501Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw34501step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34501step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34501step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34502step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34502step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34503Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34503step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34503step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34503step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34503step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34503step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34504step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34504step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34504step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34505Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34505step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34505step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34505step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34505step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34505step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34506step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34506step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34506step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34507Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34507step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34507step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34508step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34508step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34508step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34509step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34509step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34509step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34510step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34510step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34510step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34511step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34511step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34511step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34512step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34512step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34512step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34513step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34513step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34513step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34514step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34514step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34514step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw34515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34515step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34515step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34515step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw34516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw34516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw34517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw34517step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw34517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34518step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34518step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34519step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34519step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34520step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34520step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw34521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34521step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34521step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw34522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34522step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34523step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34524step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw34525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34525step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34525step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw34526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34526step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34527step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34528step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34529step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw34530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34530step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34536 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw34536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34536step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34536step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34536step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34536step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34539 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34539step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34539step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34556 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34556step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34556step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3471step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw3471step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3475step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw3475step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3475step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw3475step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3475step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3475step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3475step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3475step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3501step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3501step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3501step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw3501step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3501step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def raw3501step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3502step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3502step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3502step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3502step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3502step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3505step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3505step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3505step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw3505step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3505step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw3505step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3511step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3511step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw3511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3512step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw3512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3512step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3512step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw3513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3513step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3513step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw3514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3514step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3515step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![3, -3, 0]]
def raw3515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3515step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -2, 3], ![-3, 3, 0]]
def raw3515step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3515step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw3515step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3516step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]
def raw3516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3516step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw3516step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3516step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw3516step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3517 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![3, -3], ![0, 0]]
def raw3517Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3517step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![3, -3]]
def raw3517step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3517step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![3, -3]]
def raw3517step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3517step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3]]
def raw3517step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3517step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw3517step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3520step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3521step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw3521step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3522step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![4, -4, 0]]
def raw3522step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3523step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-3, 3, 0]]
def raw3525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3525step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3525step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw3526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 3, -3], ![-1, 1, 0], ![-3, 0, 3]]
def raw3530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3530step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![3, 0, -3]]
def raw3530step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 3, -3], ![-1, 1, 0], ![-3, 0, 3]]
def raw3531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3531step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![3, 0, -3]]
def raw3531step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 3, -3], ![-1, 1, 0], ![-3, 0, 3]]
def raw3532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3532step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![3, 0, -3]]
def raw3532step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![4, -4, 0]]
def raw3533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![4, -4, 0]]
def raw3533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 4, -3], ![4, -4, 0]]
def raw3533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3533step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 4, -3], ![4, -4, 0]]
def raw3533step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3533step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-4, 4, 0]]
def raw3533step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3533step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![4, -4, 0]]
def raw3533step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3564step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw3564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw3564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3565step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical270
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34560 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34560step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]
def raw34604step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34604step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34604step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34604step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw34605step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34605step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34605step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34605step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34606step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34606step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34606step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34606step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34607step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34607step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34607step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34607step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34613step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34614step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw34617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw34619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]
def raw34620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34620step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw34621step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34621step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34621step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34621step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34622step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34622step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34622step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34623step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34623step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34623step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34623step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34623step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw34624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw34624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34624step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw34624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw34625step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34625step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34626step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34626step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34626step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34627step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34627step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34627step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34627step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34627step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw34628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw34628step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34628step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw34628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34629step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34629step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34629step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34629step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34629step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34629step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34630step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34630step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34630step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34630step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]
def raw34631step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34631step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34631step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw34632step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34632step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34632step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw34633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34633step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34633step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34633step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34633step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34633step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]
def raw34634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34634step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34634step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw34635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34635step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34635step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34635step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34635step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34635step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34637step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34637step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34637step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34637step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34637step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34638step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34638step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34638step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34638step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34639step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34639step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34639step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34639step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34640step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34640step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34640step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34640step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34641step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34641step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34641step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34641step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34642step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34642step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34642step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34643step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34644step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34644step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34644step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34645step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34645step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34645step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34645step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34646step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34646step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34646step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34646step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34647step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34648step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34648step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34649step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34649step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34649step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34649step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34650step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34650step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34650step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34650step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34651step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34652step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw34653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34653step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34653step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34653step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34654 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34654step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34655step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34656 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw34656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34656step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw34657step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34657step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34657step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34657step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34657step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34658 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34658step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34659 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34659step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34659step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34660 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw34660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw34660step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34660step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34660step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34660step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34661 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw34661step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34661step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34661step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34661step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34661step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34662step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34662step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34662step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34662step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34663 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34663step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34663step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34664 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34664step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34664step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34664step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34665 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw34665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34665step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34665step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34665step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34665step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34666 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34666step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34666step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34666step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34666step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34667step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34667step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34667step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34667step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34668 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34668step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34668step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34669step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34669step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34670 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw34670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34670step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34670step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34670step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34670step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34671 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34671step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34671step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34671step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34672step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34672step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34672step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34673 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34673step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34674 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34674step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw34675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34675step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34675step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34675step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34675step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34676 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw34676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34676step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34676step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34677 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw34677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34677step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34677step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34677step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34678 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw34678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34678step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34678step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34679 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw34679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34679step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34679step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34679step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34680step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34680step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34680step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34680step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34681step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34681step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34681step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34681step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34681step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw34682step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34682step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34682step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34683step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34683step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34683step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34683step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34684step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34684step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34684step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34684step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34685step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical271
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw34697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw34701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34702step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34702step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34702step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34702step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34703step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34703step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34703step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw34704step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34704step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34704step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34705step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34705step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34705step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34705step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34705step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34706step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34706step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34707step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34708step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34708step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34708step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34709step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34709step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34711step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34711step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34711step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34711step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34711step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34712step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34712step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34712step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34712step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34713step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34713step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34714step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34714step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34714step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34715step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34715step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34715step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34716step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34716step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34717step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34717step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34717step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34718step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34718step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34718step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw34719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34719step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34719step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34719step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34720step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34720step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34720step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34721step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34722step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34722step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw34723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34723step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34723step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34723step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34724Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34724step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![1, -1], ![1, -1], ![1, -1]]
def raw34724step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34724step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw34724step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34725Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34725step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34725step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw34725step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34725step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34725step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw34726Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34726step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34726step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw34726step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34726step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34726step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw34727Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34727step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34727step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw34727step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34727step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34727step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34728step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![1, -1], ![1, -1]]
def raw34728step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34728step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw34728step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw34729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw34729step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34729step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw34729step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34729step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34729step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw34730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw34730step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34730step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw34730step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34730step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34730step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw34731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34731step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![2, -2], ![1, -1]]
def raw34731step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34731step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw34731step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw34732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34732step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34732step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34732step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-3, 3, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw34738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw34738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34739 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]
def raw34739Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34739step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]
def raw34739step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34739step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]
def raw34739step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34739step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw34739step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw34742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw34742step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -2, 0]]
def raw34744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -2, 0]]
def raw34744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw34744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw34744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw34745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw34745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw34745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw34745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34746 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![0, 0]]
def raw34746Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34746step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-2, 2], ![0, 0], ![-1, 1], ![2, -2]]
def raw34746step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34746step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-2, 2], ![-1, 1], ![2, -2]]
def raw34746step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34746step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw34746step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 2, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34764step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw34769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34769step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34772Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0], ![2, 0, -2]]
def raw34773Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34773step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34773step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw34774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34774step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34774step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34775Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34775step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34776Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34777Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw34778Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34778step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw34779Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34779step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34780Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34780step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw34781Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34781step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34782step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34782step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34782step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34782step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34782step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34783step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34783step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34783step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34783step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34784step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34784step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34784step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34784step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34785step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34785step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34785step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34785step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34786step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34786step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34786step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34787step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34788step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34788step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34789step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34789step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34790step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34790step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34791step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw34791step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34791step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw34791step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34792step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34792step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34792step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34792step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34793step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34793step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34793step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34793step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34794step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34794step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34794step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34794step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34794step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34795step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw34795step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34795step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw34795step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34796step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34796step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34797step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34797step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34798Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34798step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34798step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34798step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34799Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34799step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34799step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34800Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34800step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34801Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34801step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34801step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34802step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34802step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34803step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34805step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34806step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34807step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34809step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34810step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34810step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw34810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34811Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34811step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34812Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34812step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34813Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34813step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34813step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34813step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34813step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34813step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34813step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34814step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34814step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34814step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw34814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34815step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical272
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34816step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34816step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34817 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34817step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34817step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, 0, 2], ![0, -2, 2]]
def raw34817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34817step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw34817step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34817step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34817step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34817step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34817step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34818 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34818step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34819 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34819step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34819step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34820 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-3, 1, 2], ![0, -2, 2]]
def raw34820step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34820step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34821 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-2, 0, 2], ![-1, -1, 2]]
def raw34821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34821step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34821step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34821step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34822step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![-2, 0, 2], ![0, -2, 2]]
def raw34822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34822step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw34822step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34822step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw34822step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34823 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34823step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34823step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34824 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34824step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34825 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-3, 1, 2], ![0, -2, 2]]
def raw34825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34825step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw34825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34826 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34826step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-2, 0, 2], ![-1, -1, 2]]
def raw34826step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34826step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34826step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34826step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34826step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34827step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34827step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34827step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34827step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34828 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34828step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34828step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34829 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34829step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34830 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34831 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34831step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34831step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34831step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34831step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34832step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34832step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34832step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34832step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34832step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34833 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34833step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34833step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34833step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34834 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34834step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34834step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34835 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34835step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34836 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34836step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34836step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34836step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34836step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34837step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![-1, -1, 2], ![0, -2, 2]]
def raw34837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34837step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34837step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34837step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34837step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34837step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34837step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34838 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34838step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, -1, 2], ![0, -2, 2]]
def raw34838step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34838step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34838step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34838step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34839 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34839step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34839step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34839step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34839step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34839step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34839step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34840 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34840step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34840step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34840step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34840step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34840step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34841 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw34841step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34841step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34841step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34841step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34841step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![-2, 0, 2], ![1, -3, 2]]
def raw34842step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34842step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw34842step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34842step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw34842step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34843 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-2, 0, 2], ![1, -3, 2]]
def raw34843step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34843step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34843step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34843step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34843step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34844 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34844step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34844step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34844step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34845 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34845step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34846 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw34846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw34846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34846step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-3, 1, 2], ![1, -3, 2]]
def raw34846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34846step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw34846step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34847step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34847step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34847step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34847step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34848step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34848step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34849step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34849step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34849step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34849step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34850step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34850step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34850step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34850step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34850step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34850step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34850step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34851step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34851step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34851step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34851step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34852step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34852step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34853step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34854step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34855step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34856step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34856step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34857step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34859step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34859step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34859step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34860step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34860step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34860step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34860step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34861step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34861step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34861step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34861step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34862step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34862step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34862step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34862step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34862step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34862step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34862step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34863step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34863step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34863step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34863step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34864step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34864step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34864step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34864step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34865step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34865step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34865step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34865step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34866step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34866step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34866step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34867step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34868step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34869step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34869step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34869step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34870step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34870step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34871step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34873step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34874step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34875step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34877step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34878step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34878step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34878step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34878step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34879step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34879step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34879step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34880step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34880step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34881step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34881step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34881step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34881step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34881step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34881step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34882step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34882step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34883step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34883step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34884step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34885 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34885step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw34885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34885step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34885step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34885step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34885step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34886 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34886step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34886step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34886step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34887step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34887step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34888 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34888step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34888step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34888step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34888step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw34889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw34889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34889step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw34889step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34890 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34890step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34890step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34891 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34891step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34892 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34892step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34892step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34893step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34893step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34893step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34893step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34894 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34894step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34895 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34895step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34896 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34896step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34896step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34896step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34896step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34897step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34897step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34897step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34897step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34898 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34898step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34899 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34899step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34900 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34900step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34900step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34900step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34900step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34900step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, -2, 2], ![-1, -1, 2]]
def raw34901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34901step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34901step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34901step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34901step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34901step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34902 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2]]
def raw34902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34902step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34902step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34902step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34902step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34903 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34903step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34903step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34903step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34903step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34903step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34904 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34904step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34904step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34904step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34904step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34904step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34905 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw34905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw34905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 0, 2]]
def raw34905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34905step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34905step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34905step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34905step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34906 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-2, 0, 2], ![0, -2, 2]]
def raw34906step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34906step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34906step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34906step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw34942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34942step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw34943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34943step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical273
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34944step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34944step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw34945step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw34945step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34946step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34946step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34948step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34948step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34950step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34950step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34950step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34951step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34952step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34953step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw34954step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw34954step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34955step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw34955step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw34955step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34956step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34957step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34957step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34957step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw34958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw34958step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34958step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34958step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34959step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw34959step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34959step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw34959step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34960step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34960step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34961step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34961step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34961step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34961step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34961step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34962step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34962step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34962step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34962step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34962step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34964step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw34965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw34967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34973step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34973step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34975step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34976step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw34976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34977step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw34977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34979step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw34980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw34980step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34980step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw34980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34981step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw34981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34982step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw34982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34983step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34984step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34984step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34985step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34985step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34985step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34985step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34985step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34986step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34987step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34988step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34989step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw34989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34989step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34989step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34989step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34990step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34990step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34990step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34991step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34991step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34991step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34992step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34993step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34993step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34994step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw34994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34994step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34994step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34994step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34995step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34995step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34996step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34996step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34997step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34997step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34997step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw34998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw34998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34998step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw34998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw34999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw34999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35000step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35000step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35001step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw35002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw35002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35003step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw35003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw35003step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35003step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw35003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35004step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw35004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw35004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35005step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw35006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw35006step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw35010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw35011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35011step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw35012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35012step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw35013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35013step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35016 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35016step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35016step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35016step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35016step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical274
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw35115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![2, 0, -2], ![2, -1, -1]]
def raw35115step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35115step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35115step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35116step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35116step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35116step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35116step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35116step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35117step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35117step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35117step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35117step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35117step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 1, -2], ![2, -1, -1]]
def raw35118step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35118step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35118step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35118step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35118step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35118step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35118step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35119step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![2, 0, -2], ![1, 0, -1]]
def raw35119step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35119step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35119step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35119step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35119step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35119step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35119step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, 0, -2], ![2, -1, -1]]
def raw35120step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35120step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35120step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35120step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw35121step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35121step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35121step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35121step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw35122step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35122step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35122step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35122step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 1, -2], ![2, -1, -1]]
def raw35123step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35123step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw35123step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35123step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35123step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35123step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35123step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![2, 0, -2], ![1, 0, -1]]
def raw35124step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35124step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw35124step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35124step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw35124step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35124step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw35124step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35125step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35125step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35125step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35126step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35127step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35127step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35127step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35127step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35128step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35128step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35128step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35128step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35129step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35129step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35129step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35129step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35130step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35130step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35132step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35132step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35132step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35132step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35133step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35133step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35133step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35133step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35134step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35134step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35134step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35134step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35135step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![3, -1, -2], ![2, -1, -1]]
def raw35135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35135step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw35135step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35135step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw35135step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![3, -1, -2], ![2, -1, -1]]
def raw35136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35136step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw35136step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw35137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35137step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw35137step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw35138step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw35138step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![3, -1, -2], ![1, 0, -1]]
def raw35139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35139step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw35139step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35139step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw35139step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35140step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, 0, -2], ![3, -2, -1]]
def raw35140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35140step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw35140step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35140step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw35140step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35141step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, 0, -2], ![3, -2, -1]]
def raw35141step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35141step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35141step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35142step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35142step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35142step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35142step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35143step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35143step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35143step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35143step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw35144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw35144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35144step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw35144step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35144step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35144step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35144step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35144step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35144step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35144step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35145Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35145step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35145step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![2, 0, -2], ![2, -1, -1]]
def raw35145step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35145step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -2, 0], ![2, -1, -1]]
def raw35145step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35146Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35146step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 2, 0]]
def raw35146step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw35146step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35147Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35147step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 2, 0]]
def raw35147step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw35147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35148Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35148step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 1, -2], ![2, -1, -1]]
def raw35148step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35148step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw35148step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35148step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw35148step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35149Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35149step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![2, 0, -2], ![1, 0, -1]]
def raw35149step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35149step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw35149step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35149step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw35149step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35150Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35150step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, 0, -2], ![2, -1, -1]]
def raw35150step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35150step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35150step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35151Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35151step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw35151step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35151step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35152Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35152step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw35152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35152step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35153Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35153step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35153step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 1, -2], ![2, -1, -1]]
def raw35153step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35153step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw35153step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35153step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35153step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35154Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35154step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![2, 0, -2], ![1, 0, -1]]
def raw35154step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35154step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw35154step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35154step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw35154step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35155Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35155step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35155step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw35157step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35158step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw35158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35159step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw35159step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw35159step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35160step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35161step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw35162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35162step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35163step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw35163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35164step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw35164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw35164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![3, -1, -2], ![2, -1, -1]]
def raw35165step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35165step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw35165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35166step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![3, -1, -2], ![2, -1, -1]]
def raw35166step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35166step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-2, 0, 2], ![-3, 3, 0]]
def raw35166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35166step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, 0, -2], ![3, -3, 0]]
def raw35166step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![3, -1, -2], ![1, 0, -1]]
def raw35169step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35169step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![-2, 3, -1], ![-2, 0, 2]]
def raw35169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35169step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw35169step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, 0, -2], ![3, -2, -1]]
def raw35170step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw35170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, 0, -2], ![3, -2, -1]]
def raw35171step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35171step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-2, 0, 2], ![-3, 3, 0]]
def raw35171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35171step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, 0, -2], ![3, -3, 0]]
def raw35171step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw35174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw35174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35174step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw35174step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35174step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35174step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35174step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35175step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![2, 0, -2], ![2, -1, -1]]
def raw35175step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35175step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35175step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35175step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35175step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35175step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35175step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35176step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35176step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35176step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35176step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35176step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35177step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35177step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35177step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35178step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 1, -2], ![2, -1, -1]]
def raw35178step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35178step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35178step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35178step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35178step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35178step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35178step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35179step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35179step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![2, 0, -2], ![1, 0, -1]]
def raw35179step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35179step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35179step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35179step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35179step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35179step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35179step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35180step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, 0, -2], ![2, -1, -1]]
def raw35180step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35180step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, -1, 2], ![-2, 3, -1]]
def raw35180step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35180step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw35180step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35180step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw35180step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35181step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35181step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35181step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35181step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35181step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35182step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35182step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35182step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35182step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35183step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 1, -2], ![2, -1, -1]]
def raw35183step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35183step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw35183step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35183step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw35183step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35183step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw35183step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35184step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![2, 0, -2], ![1, 0, -1]]
def raw35184step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw35184step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35184step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw35184step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35184step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw35184step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35185step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw35185step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw35185step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35185step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw35185step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35186step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35186step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35186step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35186step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35187step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35187step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35188step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35188step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35188step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35189step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35189step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35189step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw35190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw35190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35190step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw35190step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35191step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35191step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35191step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35191step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35191step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35192step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35192step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35193step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35193step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35193step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35193step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35193step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35194step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35194step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35194step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35194step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35195step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![3, -1, -2], ![2, -1, -1]]
def raw35195step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35195step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 3, -2], ![-1, -1, 2], ![-1, -2, 3]]
def raw35195step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35195step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw35195step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35195step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw35195step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35196step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![3, -1, -2], ![2, -1, -1]]
def raw35196step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35196step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -1, 2], ![-2, -1, 3]]
def raw35196step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35196step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw35196step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35196step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw35196step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35197step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw35197step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw35197step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35197step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw35197step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35198step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw35198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw35198step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35198step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw35198step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35199step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35199step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![3, -1, -2], ![1, 0, -1]]
def raw35199step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35199step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-2, -1, 3]]
def raw35199step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35199step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw35199step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35199step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw35199step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical275
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw35200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35200step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, 0, -2], ![3, -2, -1]]
def raw35200step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35200step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-2, -1, 3]]
def raw35200step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35200step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw35200step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35200step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw35200step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35201step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, 0, -2], ![3, -2, -1]]
def raw35201step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35201step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw35201step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35201step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw35201step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35201step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw35201step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35202step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw35202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw35202step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw35202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35203step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw35203step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw35203step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35203step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw35203step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw35204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw35204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw35204step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35204step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -2, 3], ![-2, 1, 1]]
def raw35204step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35204step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw35204step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35204step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw35204step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw35222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35222step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35222step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35222step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35222step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw35223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw35224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35224step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35224step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw35225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw35225step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35226step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35226step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35226step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35227step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35227step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35229step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35230step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35232step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![3, -2, -1], ![2, -1, -1]]
def raw35232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35232step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw35232step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35232step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw35232step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35233step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35233step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35233step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35233step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35233step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35234step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35234step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35234step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35234step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw35235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw35235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![3, -2, -1], ![1, 0, -1]]
def raw35235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35235step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35235step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35235step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35235step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35235step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35235step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35236step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -1, -1], ![3, -2, -1]]
def raw35236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35236step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw35236step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35236step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw35236step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35237step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35237step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35237step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35237step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35238step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35238step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35238step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35238step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35238step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35239step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw35239step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35239step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35239step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35240step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw35240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35240step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35240step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35241step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw35241step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35241step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35241step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35242step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw35242step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35242step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw35243step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35243step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35243step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35244Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35244step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35244step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35245Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35245step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35246Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35246step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35247Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35247step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35247step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35248step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35249step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35250step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35251step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35251step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35252step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35252step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![3, -2, -1], ![2, -1, -1]]
def raw35252step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35252step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw35252step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35253step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35253step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35253step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35254step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw35255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw35255step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![3, -2, -1], ![1, 0, -1]]
def raw35255step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35255step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35255step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35255step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35256step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -1, -1], ![3, -2, -1]]
def raw35256step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35256step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw35256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35257step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35257step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35257step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35259 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw35259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35259step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35259step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35259step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35259step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35260 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35260step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35260step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35261 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35261step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35262 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-2, 0, 2], ![-1, -1, 2]]
def raw35262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35262step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35262step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35262step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35262step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35263 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw35263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35263step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35263step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35263step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35264 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35264step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35264step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35264step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35265 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35265step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35266 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35266step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35266step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35266step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35266step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35267 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35267step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35267step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35267step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35267step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35268 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35268step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35268step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35269 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35269step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35269step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35269step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35270 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35270step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35270step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35270step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35270step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35271 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2]]
def raw35271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35271step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35271step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35271step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35271step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35272 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35272step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35272step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35272step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35272step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35273 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35273step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35273step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35273step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35273step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35274 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw35274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw35274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35274step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -2, 2], ![-2, 0, 2]]
def raw35274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35274step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35274step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35274step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35274step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35274step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35274step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35275 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw35275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw35275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, -1, 2], ![0, -2, 2]]
def raw35275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35275step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35275step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35275step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35275step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35276 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw35276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw35276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35276step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35276step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35276step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35276step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35277 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw35277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw35277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35277step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35277step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35277step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35277step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35278step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw35279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw35280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35280step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw35281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35281step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35281step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35282step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35283step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35285step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35287step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw35288step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw35288step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35290step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw35291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw35291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35291step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw35292step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw35292step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35293step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35293step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35293step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35293step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35293step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35294step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35294step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35294step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35294step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35317step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw35317step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw35317step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35317step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw35317step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35319step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35319step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35319step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35320step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35320step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35320step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35320step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35321Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35321step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35321step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35321step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35322step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35323Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35323step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35324step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw35324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw35324step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35324step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw35324step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35325Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw35325step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw35325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35326step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw35326step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw35326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35327Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35327step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw35327step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw35327step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35327step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw35327step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical276
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw35328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35328step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35329Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35329step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35329step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw35330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw35330step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35330step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35331Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35331step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw35331step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw35331step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35331step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw35331step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35332step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35333Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35333step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35333step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35335step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35337step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw35338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw35339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35339step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35340step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35341step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35342step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35345step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35416step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw35416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35416step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw35417step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35417step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35418step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw35418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35418step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![2, 0, -2], ![1, 0, -1]]
def raw35419step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35419step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw35419step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw35419step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw35419step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw35419step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw35419step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35420step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35422step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35423step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35425step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35426step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35426step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw35426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35426step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw35426step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw35427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35427step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw35428step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35428step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35429step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![3, -1, -2], ![1, 0, -1]]
def raw35429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35429step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw35429step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35429step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35429step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw35430step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35430step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35430step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw35431step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35431step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35431step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35431step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35432step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw35432step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35432step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35432step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35432step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35433Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35433step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw35433step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35433step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35433step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35433step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35433step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35433step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35433step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35434Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35434step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35434step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35434step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35435Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35435step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35435step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35436Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35436step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35436step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![2, 0, -2], ![1, 0, -1]]
def raw35436step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35436step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw35436step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35436step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw35436step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35437Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35437step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35437step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35437step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35437step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35437step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35438Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35438step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35439Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35439step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35439step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35439step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35439step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35439step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35440Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35440step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35440step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35440step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35440step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35440step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35441Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35441step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35441step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35442step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35442step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35442step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35442step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35442step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35443step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw35443step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35443step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw35443step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35443step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw35443step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35444step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35444step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35445step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35445step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35446step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![3, -1, -2], ![1, 0, -1]]
def raw35446step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35446step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35446step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35446step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35446step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35447step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35447step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw35447step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35447step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw35447step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35447step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw35447step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35447step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw35447step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35448step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw35448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw35448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35449step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw35449step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw35449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical277
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw35534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 3, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35534step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35534step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![2, -2], ![2, -2]]
def raw35534step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35534step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw35534step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35535step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![2, -2], ![2, -2]]
def raw35535step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35535step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw35535step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35535step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw35535step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35536step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35536step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![2, -2], ![2, -2]]
def raw35536step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35536step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw35536step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35536step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw35536step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35537step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35537step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![1, -1], ![2, -2], ![2, -2]]
def raw35537step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35537step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw35537step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35538step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![-1, 1], ![2, -2], ![2, -2]]
def raw35538step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35538step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw35538step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw35539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw35539step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35539step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![2, -2], ![1, -1]]
def raw35539step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35539step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw35539step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35540step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35540step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![1, -1], ![2, -2], ![2, -2]]
def raw35540step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35540step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw35540step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35541step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw35541step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw35542Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw35542step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![3, -3, 0], ![2, -2, 0]]
def raw35542step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35542step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![3, -3], ![2, -2]]
def raw35542step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35542step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]
def raw35542step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw35543Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw35543step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35543step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![3, -3], ![2, -2]]
def raw35543step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35543step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw35543step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35543step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw35543step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw35544Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw35544step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35544step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![3, -3], ![2, -2]]
def raw35544step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35544step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw35544step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35544step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw35544step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, -1, 0]]
def raw35545Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![1, -1, 0]]
def raw35545step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![3, -3, 0], ![1, -1, 0]]
def raw35545step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35545step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![3, -3], ![1, -1]]
def raw35545step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35545step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw35545step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35545step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw35545step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw35546Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw35546step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![2, -2, 0], ![3, -3, 0]]
def raw35546step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35546step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![2, -2], ![3, -3]]
def raw35546step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35546step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]
def raw35546step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw35547Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw35547step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35547step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![2, -2], ![3, -3]]
def raw35547step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35547step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw35547step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35547step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw35547step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw35548Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw35548step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35548step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![2, -2], ![3, -3]]
def raw35548step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35548step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw35548step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35548step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw35548step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35549step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35549step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35549step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw35550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw35550step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35550step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35550step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35551step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35551step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw35552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35552step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35553step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35553step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35553step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35553step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35554step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw35555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35555step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35555step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35556step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35556step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35556step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35556step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw35557step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw35558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35558step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35558step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw35558step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35558step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35558step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw35561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw35561step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35561step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw35563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35563step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35565step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35565step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35565step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35565step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw35566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw35566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35566step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35566step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35566step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35566step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw35567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw35567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw35568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35568step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35568step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35568step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35568step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw35569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw35569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw35569step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35569step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35569step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35569step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw35570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35570step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35570step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35570step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw35571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw35571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35571step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35571step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35571step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35571step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35572 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35572step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35572step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35572step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35572step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35573 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35573step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35573step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35574 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35574step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35575 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw35575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw35575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35575step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35575step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35576 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35576step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35576step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, 0, 2]]
def raw35577step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw35577step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35577step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw35577step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35578 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw35578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35578step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw35578step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35579 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35579step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw35579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35579step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35579step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35580 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw35580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw35580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw35580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35580step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35581 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35581step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35581step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw35582step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35582step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35582step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35582step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35583 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35583step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35583step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical278
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw35584 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35584step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35585 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw35585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35585step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35585step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35585step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35586 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35586step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35586step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35587step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35587step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35587step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35587step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35587step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35588 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35588step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35588step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35589 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35589step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35590 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw35590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw35590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35590step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35590step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35591 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35591step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35591step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw35592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw35592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35592step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35592step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35592step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35592step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35593 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw35593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw35593step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35593step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35593step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35594 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw35594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35594step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35594step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35594step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35595 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw35595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw35595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35595step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35595step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35596 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35596step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35596step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35596step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw35597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw35597step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw35597step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35597step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw35597step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35597step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw35597step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35598 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw35598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw35598step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35598step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35598step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35599 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw35599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35599step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35599step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35599step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35600 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw35600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw35600step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35600step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35600step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35600step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35601 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw35601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw35601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35601step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35601step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35601step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35602step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35603step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw35604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw35604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35604step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw35604step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35604step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw35604step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw35605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw35605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw35605step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw35605step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35606step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw35607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35607step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35608step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35608step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35609step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35609step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35609step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35609step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw35610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw35610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35610step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35610step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35610step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35610step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35610step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw35611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw35611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35611step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35611step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw35612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw35612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw35612step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw35612step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw35613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35613step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35613step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35613step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35613step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35613step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw35614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw35614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35614step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35614step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35614step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35614step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35615 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35615step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35615step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35615step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35616 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35616step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35616step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35617 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35617step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35617step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35618 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35618step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35618step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw35619step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw35619step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35620 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35620step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35621 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35621step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35622 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35622step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35622step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35623step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35623step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35623step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35623step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35624 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35624step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35624step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35625 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35625step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35626 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35626step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35626step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35627step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35627step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35627step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35627step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35628 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35628step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35628step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35628step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35629 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35629step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35630 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35630step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35630step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw35631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw35631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35631step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35631step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35631step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35631step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35631step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35632 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw35632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw35632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35632step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35632step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35632step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35633 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw35633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35633step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35633step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35634 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw35634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw35634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35634step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35634step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35635 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35635step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35635step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35636 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35636step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35636step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end


