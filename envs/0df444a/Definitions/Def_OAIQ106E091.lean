-- Prove2me | Definitions.Def_OAIQ106E091
-- name    : OAIQ106E091
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:03:21.103166+00:00
-- url     : https://prove2.me/theorems/326ebb84-7b83-4597-b1bc-873b0f43a853
-- title:
--   Definitions bundle OAIQ106E091 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7306 declarations of OpenAI's Lean: 7306 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw14751`, `OAI.MUB6.Certificate.MixedSemantics.raw14751step0`, `OAI.MUB6.Certificate.MixedSemantics.raw14751step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14751step1`, `OAI.MUB6.Certificate.MixedSemantics.raw14751step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14752`, `OAI.MUB6.Certificate.MixedSemantics.raw14752Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14752step0`, `OAI.MUB6.Certificate.MixedSemantics.raw14752step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14752step1`, `OAI.MUB6.Certificate.MixedSemantics.raw14752step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14753`, `OAI.MUB6.Certificate.MixedSemantics.raw14753Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14753step0`, `OAI.MUB6.Certificate.MixedSemantics.raw14753step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14753step1`, `OAI.MUB6.Certificate.MixedSemantics.raw14753step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14754`, `OAI.MUB6.Certificate.MixedSemantics.raw14754Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14754step0`, `OAI.MUB6.Certificate.MixedSemantics.raw14754step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14754step1`, `OAI.MUB6.Certificate.MixedSemantics.raw14754step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14754step2`, `OAI.MUB6.Certificate.MixedSemantics.raw14754step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14755`, `OAI.MUB6.Certificate.MixedSemantics.raw14755Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14755step0`, `OAI.MUB6.Certificate.MixedSemantics.raw14755step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14756`, `OAI.MUB6.Certificate.MixedSemantics.raw14756Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14756step0`, `OAI.MUB6.Certificate.MixedSemantics.raw14756step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14757`, `OAI.MUB6.Certificate.MixedSemantics.raw14757Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14757step0`, `OAI.MUB6.Certificate.MixedSemantics.raw14757step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14758`, `OAI.MUB6.Certificate.MixedSemantics.raw14758Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw14758step0` and 7266 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical1`, `MutuallyUnbiased_MixedSemantics_Canonical11`, `MutuallyUnbiased_MixedSemantics_Canonical115`, `MutuallyUnbiased_MixedSemantics_Canonical116`, `MutuallyUnbiased_MixedSemantics_Canonical117`, `MutuallyUnbiased_MixedSemantics_Canonical118`, `MutuallyUnbiased_MixedSemantics_Canonical119`, `MutuallyUnbiased_MixedSemantics_Canonical12`, `MutuallyUnbiased_MixedSemantics_Canonical120`, `MutuallyUnbiased_MixedSemantics_Canonical121`, `MutuallyUnbiased_MixedSemantics_Canonical122`, `MutuallyUnbiased_MixedSemantics_Canonical123`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound48_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound50_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound52_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound53_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero818_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound804_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound834_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound891_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound44_e`.
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

def raw14Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw14step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw14step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]

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

def raw147Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw147step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw152 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw152Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw152step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw153 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw153Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw153step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw154 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw154Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw154step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw154step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw154step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw155 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw155Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw155step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw155step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw156 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw156Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw156step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw156step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw157 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw157Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw157step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw157step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw158 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-2, 1, 1], ![0, 2, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1475Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw1475step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1475step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1475step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1475step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1476 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1476step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1477 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1478 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1478Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw1478step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1478step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1478step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1478step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1479 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1479step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1480 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1481 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1481Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1481step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1481step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1481step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1482 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1482step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1483 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1483Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1484 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1484Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw1484step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1484step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1484step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1485 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1485step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1485step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1485step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1486 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1486Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1487 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1487Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1487step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1487step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1487step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1487step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1488 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw1488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw1488step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw1488step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1489 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw1489Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw1489step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1490 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw1490Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw1490step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw1490step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1490step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw1490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1491 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1491step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1491step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1492 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1492Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1492step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1493 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1493Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw1493step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1493step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1493step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1494 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1494step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1494step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1495 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1496 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1496Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw1496step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1500 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1500Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1500step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1500step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1501 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1502 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1502Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw1502step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1502step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1503 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1503Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1503step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1503step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1503step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1504 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1505 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1505Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw1505step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1505step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1505step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1505step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1505step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1506 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1506step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1506step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1507 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1508 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1508Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw1508step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1508step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1509 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1509step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1509step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1510 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1511 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1511Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-3, 1, 2]]
def raw1511step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw1511step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw1511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1512 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1512step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1512step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1513 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1514 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1514Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1514step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1514step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1514step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1515 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1515step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1515step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1516 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1517 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1517Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw1517step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw1517step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw1517step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1521 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1521step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1522 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1523 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1523Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw1523step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw1523step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1523step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw1523step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1524 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1524step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1525 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1526 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1526Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw1526step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw1526step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw1526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1527 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 2, -3], ![-2, 3, -1]]
def raw1527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1527step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw1527step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw1527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1528 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 2, -3], ![-2, 3, -1]]
def raw1528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1528step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw1528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1529 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 2, -3], ![-2, 3, -1]]
def raw1529Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1529step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, -2, 3], ![-3, 1, 2]]
def raw1529step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 2, -3], ![3, -1, -2]]
def raw1529step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 2, -3], ![3, -1, -2]]
def raw1529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1530 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1530step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1531 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1532 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1532Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw1532step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1532step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw1532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw14751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]

def raw14751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw14751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw14751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14752 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14752Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14752step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14753 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14753Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw14753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14753step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14753step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14754 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14754Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14754step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14755 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw14755Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14756Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14757 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14757Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14758 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14758Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14759 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14759Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14759step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14760 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw14760Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14761 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14761step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14761step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14761step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14762 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14762Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14762step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14762step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14762step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14762step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14763 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14763Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14763step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14763step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14763step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14763step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14763step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14764 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14764Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14764step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14764step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14764step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14765 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14765Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14765step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14765step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14765step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14765step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14765step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14766Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14766step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14766step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14766step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14767 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14767Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14767step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14767step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14767step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14767step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14767step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14768 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14768Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14768step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14768step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14768step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14768step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14768step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14769 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14769Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14769step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14769step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14769step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14769step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14770 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14770Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14770step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14770step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14770step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14770step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14771Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14771step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14771step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14771step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14771step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14771step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14772 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14772Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14772step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw14772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw14772step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14772step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw14772step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14773 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14773Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14773step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2]]
def raw14773step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14773step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14773step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14773step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14773step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14773step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14773step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14774 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14774Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14774step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14774step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14774step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14774step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14774step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14775 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14775Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14775step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14775step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14775step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14775step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14775step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14776Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 2, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw14776step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw14776step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14776step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw14776step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14777 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14777Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14777step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14777step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14777step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14778 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14778Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14778step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14779 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14779Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14779step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14780 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14780Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14780step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14780step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14780step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14780step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14780step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14781Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw14781step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw14781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14782 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14782Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14782step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14782step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14782step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14783 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14783Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14783step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14783step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14784 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14784Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14784step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14784step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14785 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw14785Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw14785step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14785step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw14785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14786Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14786step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14786step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14786step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14787 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14787Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14787step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14788 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14788Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14788step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14788step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14788step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14789 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14789Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14789step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14789step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14790 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw14790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14790step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14790step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14790step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14791 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14791Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14792 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14792Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14792step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14793 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14794 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14795 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14796 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14797 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![-2, 2]]
def raw14797Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14797step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![-1, 1], ![-2, 2]]
def raw14797step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14797step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-2, 2]]
def raw14797step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14797step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw14797step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14799 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14799Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14799step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14800 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14800Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14800step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14801 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14802 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14802step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14803 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14803Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14804 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14805 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14806 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14806Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw14806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14807 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14808 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14809 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14809Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw14809step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14809step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14810Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14810step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14810step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14810step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14811 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14812 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14812step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw14845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14845step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14846step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14847step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw14848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14848step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw14851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14852Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14853Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14854Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14855Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14856Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw14859Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw14859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw14860Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw14860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw14861Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14861step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw14862Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14863Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw14864Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw14864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw14864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw14865Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw14865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw14866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw14867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw14867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw14867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw14868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14876step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14876step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14876step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw14876step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14876step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw14876step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14877step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14877step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14877step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14877step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14878step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14878step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14878step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14878step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14878step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw14879step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14879step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw14879step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14880step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14880step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14881step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14881step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14881step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14881step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14881step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14883step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14883step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14884step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14884step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14884step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14886step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw14886step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw14887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14887step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw14888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw14889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw14889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw14889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw14890step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14890step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14890step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14890step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14890step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14891step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14891step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14891step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14891step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14892step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14892step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14892step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14892step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14893Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14893step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14893step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14893step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw14893step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14894Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14894step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14895Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14895step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14895step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14895step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw14896Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw14896step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw14896step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw14896step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14897Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14897step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14897step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw14897step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14898Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14898step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14898step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14899Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw14900Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw14900step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14900step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14900step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14901Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14901step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw14901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14902Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14902step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14903Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw14904Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw14904step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14904step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14904step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14905Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14905step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw14905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14906Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14906step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14906step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw14906step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14907Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14907step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14908Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14908step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14908step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14908step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw14909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw14909step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw14909step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14909step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14909step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14910step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14910step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14910step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw14910step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14910step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14910step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14911step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14911step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14912step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14913step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14913step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14913step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14913step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14913step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14914step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14914step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14915step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14915step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14915step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14916step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14916step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14916step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14916step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14916step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw14916step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14917step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14917step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14917step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14917step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14917step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14918step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14918step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14918step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14918step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14918step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14918step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14919step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14919step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14920step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14920step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14920step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14920step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14921step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw14921step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14921step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw14921step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14922step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14922step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14922step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14922step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14922step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14922step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14922step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14922step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14923step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14923step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14924step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14924step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14925step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14925step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14926step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14926step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14926step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14927step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14927step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14927step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14928step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14928step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14929step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14929step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14929step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14930step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14930step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14930step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14931step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14931step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14931step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14932step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14932step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw14933step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14933step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw14933step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14934step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw14934step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14934step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw14934step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14935step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14935step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14935step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14936step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14936step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14936step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw14937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw14937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![2, -3, 1], ![1, 1, -2]]
def raw14937step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14937step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw14937step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14937step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw14937step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14938step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw14938step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14938step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw14938step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw14939step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14939step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw14939step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14940step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14940step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14941step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw14942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw14942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2]]
def raw14942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14942step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14942step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14943Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14943step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14943step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14944Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14944step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14945Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14945step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14945step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14946Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14946step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14946step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14946step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14946step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14946step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14947step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14947step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14948step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14948step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14949step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14951step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14951step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw14951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14952step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14952step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw14952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14953step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14954step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14954step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14955step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14956step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14956step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14960step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14962step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14963step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw14963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14964step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14964step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14964step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw14964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14964step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw14964step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw14965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw14966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw14967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw14967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![2, -3, 1], ![1, 1, -2]]
def raw14967step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14967step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw14967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14967step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14967step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14968step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14968step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14968step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw14968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14969step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14969step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14969step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw14969step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14969step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw14969step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw14970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw14971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw14972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw14972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2]]
def raw14972step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw14972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14972step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14973 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -2, 1], ![-2, 0, 2]]
def raw14973step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14973step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14973step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14973step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14973step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14973step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14973step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14974 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14975 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2]]
def raw14975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14975step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14975step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14975step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14975step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14975step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14975step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw14976 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14976step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -2, 1], ![-3, 1, 2]]
def raw14976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14976step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -2, 1], ![-2, 0, 2]]
def raw14977step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw14977step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14977step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14977step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14977step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14977step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14978 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14978step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14979 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2]]
def raw14979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw14979step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14979step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14979step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14979step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14979step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14980 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -2, 1], ![-3, 1, 2]]
def raw14980step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14980step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14981step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14981step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14981step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14981step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14982 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14982step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14982step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14983 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14983step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14984 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14984step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14985 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14985step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14986 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14986step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -3, 1], ![-2, 0, 2]]
def raw14987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw14987step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14987step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw14987step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14987step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw14987step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14988 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -3, 1], ![-2, 0, 2]]
def raw14988step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14988step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14988step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14988step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14989 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14989step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14989step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14990 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw14990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw14990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -3, 1], ![-3, 1, 2]]
def raw14990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw14990step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14990step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw14990step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -2, 1], ![-1, -1, 2]]
def raw14991step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14991step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14991step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14991step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14991step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14991step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14991step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14992 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![-1, -1, 2]]
def raw14992step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14992step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14992step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14992step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14992step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14992step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14993 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14993step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14993step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14993step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14993step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14993step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14993step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14994 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw14994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw14994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2]]
def raw14994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14994step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14994step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14994step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14995 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14995step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -2, 1], ![-2, 0, 2]]
def raw14995step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14995step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14995step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14995step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14995step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14995step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14996 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14996step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14996step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14996step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14997 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14997step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2]]
def raw14997step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14997step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14997step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14997step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14997step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14997step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14998 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -2, 1], ![-3, 1, 2]]
def raw14998step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14998step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14998step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14998step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -2, 1], ![-2, 0, 2]]
def raw14999step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14999step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw14999step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14999step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw14999step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14999step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw14999step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15000 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw15000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw15000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15000step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15000step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15000step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15001 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2]]
def raw15001step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15001step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15001step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15001step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15001step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15002 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw15002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw15002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -2, 1], ![-3, 1, 2]]
def raw15002step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15002step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15002step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15002step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15002step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw15003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw15003step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15003step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15003step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15004 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw15004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw15004step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw15004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15004step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15004step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15004step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15005 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw15005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15005step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15005step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15005step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15006 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15007 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw15007Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw15007step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15007step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15007step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15007step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15007step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15008 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw15008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15008step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15008step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15008step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15008step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw15009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw15009step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -3, 1], ![-2, 0, 2]]
def raw15009step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15009step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw15009step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15009step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw15009step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15010 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw15010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw15010step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15010step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -3, 1], ![-2, 0, 2]]
def raw15010step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15010step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15010step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15010step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15010step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15011 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw15011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw15011step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15011step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15011step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15012 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw15012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw15012step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -3, 1], ![-3, 1, 2]]
def raw15012step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw15012step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15012step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw15012step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw15013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw15013step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -2, 1], ![-1, -1, 2]]
def raw15013step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15013step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw15013step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15013step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15013step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15013step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15013step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15014 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw15014Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw15014step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15014step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![-1, -1, 2]]
def raw15014step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15014step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15014step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15014step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15014step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15015 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw15015Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw15015step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw15015step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw15015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15016 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15016Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15016step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2]]
def raw15016step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw15016step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15016step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15016step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15016step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15017step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15017step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15017step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15017step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15018step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15018step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15018step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15018step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15018step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15019step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15019step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15019step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15019step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw15020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw15020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15020step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15020step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15020step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15020step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15021step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15021step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15021step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15021step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15022step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15023step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15023step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw15024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw15025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15027step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15029step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15030step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15031step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15031step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15031step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15031step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15032step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15032step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15032step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15032step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15033step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15033step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15033step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15033step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15033step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw15034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw15034step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15035step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15035step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15035step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15035step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15035step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15035step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15036step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15036step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15036step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15036step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15037step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15037step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15037step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15037step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw15038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw15038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw15038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15038step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15038step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15038step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15038step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15039step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15041step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15041step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15041step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15042Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw15042step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw15042step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15042step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw15042step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15042step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15042step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15043step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15043step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15044Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15044step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15044step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15044step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15044step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15044step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15045Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15046Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15047Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw15047step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15047step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15048Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15049Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15049step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15049step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15050Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15050step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15051Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15051step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15051step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15051step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15051step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw15051step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15051step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15051step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15052Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15052step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15053Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15053step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15053step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15055step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15055step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw15056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw15056step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15056step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15056step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15057step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15057step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15059step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15059step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw15060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw15060step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15060step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw15060step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15060step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15060step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15060step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15061step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15061step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15062step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15062step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15063step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15064step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15064step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15065step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15065step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15065step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15065step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15065step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15066step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15066step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15067step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15068step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15069step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15070step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15070step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15071step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15071step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15071step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15072step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15072step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15073step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15073step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15073step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15074step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15074step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15075step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15075step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15075step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15076step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw15077step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw15077step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw15078step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw15078step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw15079step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15079step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15079step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15079step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15080step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15080step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15080step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15080step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15081step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15081step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15081step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15081step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15081step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw15082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw15082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15082step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15082step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15082step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15082step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15083Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15083step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15083step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15084step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15085Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15085step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15086Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15086step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15087Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15087step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw15087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15088Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15088step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15088step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15089Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15090Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15090step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15091Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15091step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw15091step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15092Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15092step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw15092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15093Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15094Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15095Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15096Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15097Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15098Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15098step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15099Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15099step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15100Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15101Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15101step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15102Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15102step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15104step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15106step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw15106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw15107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw15107step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15108step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw15108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw15109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15110step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15110step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15111step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15111step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw15112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw15112step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15113step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15113step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15114 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15114step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15114step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15115 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15115step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15115step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15115step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15115step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15115step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15116 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15116step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15116step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15116step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15116step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15116step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15117 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15117step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15117step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15117step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15117step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15117step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15118step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15118step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15118step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15118step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15119 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15119step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15119step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15119step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15119step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15119step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15120 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15120step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15120step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15120step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15120step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15121 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15121step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15121step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15122 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15122step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15122step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15122step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15122step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15123step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15123step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15123step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15123step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15123step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15124 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15124step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15124step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15124step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15125 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15125step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15125step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15125step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15126 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15126step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15126step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15126step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15127 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15127step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15127step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15127step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15127step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15128step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15128step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15128step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15128step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15129 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15129step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15129step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15129step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15129step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15130 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15130step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15130step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15130step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15130step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15130step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15131 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15131step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15131step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15131step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15131step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15132 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15132step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15133step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15133step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15133step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15133step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15134 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15134step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15134step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15135step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15135step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15135step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15135step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15136 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15136step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15136step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15136step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15136step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15137 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15137step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15138 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15138step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 0, 1], ![0, -2, 2]]
def raw15138step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15138step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15138step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15138step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15138step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15139 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15139step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15139step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15140 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15140Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15140step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15140step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15140step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15140step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15140step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15141 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15141Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15141step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15141step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15142 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15142Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15142step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15142step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15142step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15142step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15142step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15142step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15142step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15143 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15143Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15143step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15143step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15143step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15143step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15143step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15144 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15144Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15144step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15144step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15144step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15144step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15144step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15145Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15145step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15145step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15145step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15145step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15145step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15146 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15146Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15146step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15146step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15146step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15146step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15146step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15147 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15147Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15147step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15147step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15147step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15147step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15147step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15147step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15147step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15147step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15147step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15148 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15148Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15148step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15148step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15148step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15148step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15148step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15149 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15149Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15149step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15149step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15149step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15149step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15149step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15150Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15150step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15150step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15150step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15150step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15150step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15151 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15151Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw15151step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15151step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15151step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15151step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15152 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15152Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15152step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15152step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15152step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15152step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15152step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15153 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15153Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15153step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15153step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15153step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15153step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15154 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15154Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15154step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15154step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15154step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15154step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15155Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15155step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw15155step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15155step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15155step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15155step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15156 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15156Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15156step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15156step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15157 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15157Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15157step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15158 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15158Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15158step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15158step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15159 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15159Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15159step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15159step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15159step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15159step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15159step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15160Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15160step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15160step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw15160step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15160step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw15160step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15161 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15161Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15161step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw15161step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15161step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15161step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15161step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15161step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15162Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15162step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15162step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15162step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15162step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15163 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15163Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15163step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15163step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15164 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15164step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15164step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15165 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15165Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15165step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 0, 1], ![0, -2, 2]]
def raw15165step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15165step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw15165step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15165step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw15165step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15166 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15166step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15166step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15166step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15166step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15166step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15166step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15166step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15167step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw15167step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15167step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15167step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15167step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15168step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15168step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15168step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15168step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15168step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15169step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15169step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15169step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15169step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15169step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw15170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw15170step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15170step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15170step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15170step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15170step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15171step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15171step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15172step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15172step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15172step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15172step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15172step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw15173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15173step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15174step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15174step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15174step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15176step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15176step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15176step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15176step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15176step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15177Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15177step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15177step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15177step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15177step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15178Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15178step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15178step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15178step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15178step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15178step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw15179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw15179step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15179step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15180step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15180step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15180step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15180step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15180step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15181step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15181step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15181step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15181step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15182step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15182step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15182step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15182step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15182step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15183step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw15183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15184step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15184step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15185step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw15186Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw15186step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15187Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15187step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15188Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15188step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw15189Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15189step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15190Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15190step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15191Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15191step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw15192Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw15192step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15192step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15193Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15193step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15193step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15194Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15195Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15195step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15195step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw15196Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw15196step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15196step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15196step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15197Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15197step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15197step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15197step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15198Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15198step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15199Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15199step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15199step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15199step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15200 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15200step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15200step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15200step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15201 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15202step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw15202step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw15202step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15203 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15203step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15204step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15204step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15204step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15204step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15205 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15205step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15205step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15205step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15206 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15206step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15207step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15207step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15207step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15207step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15207step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15208 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15208step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15208step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15208step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15209 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15209step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15210 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15210step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15210step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15233Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15233step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15233step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15234Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15234step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15234step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15235Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15235step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15235step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15236Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15236step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15236step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15237Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15237step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15237step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15238Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15238step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15238step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15238step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15238step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15238step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15239step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15240step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15241step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15242step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15243step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15244Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15244step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15244step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15244step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15245Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15245step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15245step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw15245step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15246Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15246step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw15247Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw15247step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw15247step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw15247step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw15248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15248step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw15249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw15249step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw15249step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw15249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw15250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw15250step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw15251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw15251step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw15251step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw15251step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw15252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15252step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw15253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw15253step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw15253step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw15253step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw15254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw15254step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15255Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15256Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15256step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15257Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15257step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15257step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15258Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15258step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15259Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15259step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15259step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15259step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15294step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw15294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw15295step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15295step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15296step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw15296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw15297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15297step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15298step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15299step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15300step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw15302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw15302step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw15303step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15304step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15306step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15307step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw15308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15309Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15309step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw15309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15310Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15310step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15311Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15311step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15312Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15312step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw15312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw15312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15313Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15313step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw15313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15314Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15314step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15315Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15315step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15316Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15317Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15317step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw15318Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw15318step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15319Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15319step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw15319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15320Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15320step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 2, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw15320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15320step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15320step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15321Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15322Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15322step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15322step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw15322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw15323Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw15323step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw15323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15323step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw15323step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15324step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15325Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15325step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15326step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15326step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15327Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15327step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15327step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15328step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15328step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15328step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15329Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15329step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15329step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15329step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15329step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15329step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15330step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15330step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15330step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15330step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15331Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15331step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15331step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15331step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15331step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15331step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15332step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15332step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15332step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15332step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15332step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15332step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15333Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15333step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw15333step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15333step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15333step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15333step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15334Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15334step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15334step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15334step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15334step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15335Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15335step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15335step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15335step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15335step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15336Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15336step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15336step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15336step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15336step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15336step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15337Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15337step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15337step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15337step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15337step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15338Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15338step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15338step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15338step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15339Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15339step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw15339step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15339step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15339step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15339step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15340Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15340step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15340step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15341Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15341step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15341step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15342Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15342step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15342step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15342step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15342step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15343Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15343step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15343step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15343step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15344Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15344step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw15344step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15344step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15344step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15344step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15344step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15345Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15345step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw15345step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15345step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15345step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15345step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15346Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15346step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15347Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15347step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15347step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15347step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15347step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw15348Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw15348step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15348step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15348step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15348step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15349Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15349step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw15349step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw15349step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15349step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw15349step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15350Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15350step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15350step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15351Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15351step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15352Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15352step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15352step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw15353Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw15353step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15353step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15353step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15355step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15355step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15355step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15356step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw15356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw15357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw15359step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15359step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw15359step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1536 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1536step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1536step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1537 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1538 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1538Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1538step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1538step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1538step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1539 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1539step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1539step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1540 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1541 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1541Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1541step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1541step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1541step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1541step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1541step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1545 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1545step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1545step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1546 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1546step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1547 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1547Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1547step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1547step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1547step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1547step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1548 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1548step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1549 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1550 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1550Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def raw1550step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def raw1550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1554 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1554step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1555 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1556 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1556Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1556step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1556step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1556step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1557 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1557step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1558 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1559 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1559Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw1559step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw1559step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw1559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1560 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1560step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1561 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1562 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1562Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1562step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1562step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1562step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1562step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1563 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1563step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1564 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1565 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1565Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1565step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1565step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1565step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1566 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1566step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1567 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1568 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1568Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1568step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1568step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1569 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1569step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1569step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1570 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1571 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1571Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1571step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1571step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1571step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1572 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1572step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1573 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1574 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1574Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1574step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1574step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1574step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1575 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1575step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1575step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1576 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1577 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1577Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw1577step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1577step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1578 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1578step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1578step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1579 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1579Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1580 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1580Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1580step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1580step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1581 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw1581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1581step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw1581step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw1581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1582 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw1582Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1582step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw1582step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1583 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw1583Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1583step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw1583step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw1583step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1584 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 2, -1], ![-1, 3, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15360 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![0, 0], ![-2, 2], ![2, -2], ![1, -1]]
def raw15360Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15360step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw15360step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15360step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw15360step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15360step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw15360step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15365step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw15368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15368step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw15369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw15372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw15373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15374step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15376step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15376step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15377step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15377step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw15378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw15378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15378step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw15379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15379step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw15380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw15381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw15382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw15382step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15382step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15382step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15383step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15383step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15383step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15383step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15383step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15384step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15385step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15385step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15385step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15385step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw15386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw15386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15386step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw15386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15386step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15386step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15386step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15386step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15386step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15386step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw15387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw15387step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15387step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15387step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15387step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15387step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15387step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw15389step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw15389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw15390step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw15390step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15390step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw15390step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw15391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw15391step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15391step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15391step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15391step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15391step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw15392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15393step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15393step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15393step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15393step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15394step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15394step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15394step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15394step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -2, 0]]
def raw15395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15395step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw15396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw15396step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15396step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw15397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw15397step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw15397step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw15397step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15397step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw15397step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw15398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15398step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15398step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15398step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15398step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw15399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw15399step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 2, 0]]
def raw15399step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15399step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw15399step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15399step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw15399step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw15400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw15400step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15400step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15400step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15400step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15400step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw15401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw15401step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw15401step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw15401step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15401step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw15401step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw15402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15402step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15402step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15402step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15402step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw15403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw15403step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw15403step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15403step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw15403step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw15404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw15404step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw15404step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15404step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15404step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15404step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15404step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15404step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15405step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15405step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15405step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15405step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15406step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15406step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15406step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15407step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15407step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15407step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15408step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15408step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15408step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15408step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15408step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15409step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15409step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15409step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15409step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15409step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15410step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15410step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15410step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15410step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15411step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15411step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15412step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15412step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15412step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15412step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15413step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15413step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15413step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15414step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15414step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15414step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15414step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15415step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15415step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15415step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15416step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15417step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15418step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15419step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15419step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw15420step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw15420step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw15421step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw15421step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15422step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15423step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15423step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15424step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15424step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15424step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15424step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15425step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15425step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15426step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw15426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15426step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw15427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15428step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15428step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw15429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw15429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15429step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15429step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw15430step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw15430step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw15431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15431step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw15432step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15433step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15433step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15433step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15433step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw15434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw15434step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15434step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15434step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15435Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15435step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15435step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15436Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15436step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15437Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15437step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15437step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15437step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15438Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15438step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15438step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15438step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15438step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15439Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15439step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15439step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15439step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15440Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15440step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15440step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15440step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15440step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15440step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15441Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15441step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15441step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15441step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15441step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15441step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15442step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15442step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15443step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15443step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15443step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15443step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15443step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15444step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw15444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15444step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15444step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15444step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15445step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15445step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15445step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15445step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15446step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15446step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15446step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15446step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15447step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15448step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15448step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15449step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15449step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15449step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15449step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw15450step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw15450step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15450step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw15450step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15451Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15451step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15451step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw15452step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw15452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15453Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15453step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15453step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15454step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15454step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15455Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15455step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw15455step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15455step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15455step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15455step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15456Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15456step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw15456step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15456step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15456step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15456step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15457Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15457step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15458Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15458step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15458step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15458step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15458step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw15459Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw15459step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15459step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15459step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15459step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15459step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15459step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15460Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15460step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw15460step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw15460step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15460step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw15460step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15461Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15461step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15461step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15461step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15462Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15462step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15463Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15463step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15463step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15463step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15463step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw15464Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw15464step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15464step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15464step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15464step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15465step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15465step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15465step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15465step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15466step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15466step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15467step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15467step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15467step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15468step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15468step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15468step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15468step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15468step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15469step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15471step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15475step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15479step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15480step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15480step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15481step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw15482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15482step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15483step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15483step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15483step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15483step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15483step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15484step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15484step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15484step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15484step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15485step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15485step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15485step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15485step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15485step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw15486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15486step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15486step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15486step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15486step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15487step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15488step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15489step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15490step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15503step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw15504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15505step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw15508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15509step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15509step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15509step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15510step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15511step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15512step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15512step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15512step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15513step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15514step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15514step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15514step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15514step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15514step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15515step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15515step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15515step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15516step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15517step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15517step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15517step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15517step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15518step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15518step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15519step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15519step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15520step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15520step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15520step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15520step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15521step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15521step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15521step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15521step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15522step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15522step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15522step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15523step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15523step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15525Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15525step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw15526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15526step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15527Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15527step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15528step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15529Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15529step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw15530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15530step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw15534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15543step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15543step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15545step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15545step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15546step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15546step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15546step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15546step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15547step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15548step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15548step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15548step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15548step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15549step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15550step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15550step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15551step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15551step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15551step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15551step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw15552step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15552step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15552step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15552step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15553step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15553step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15553step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15554step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15555step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15555step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15555step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15556step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15556step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15556step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15556step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15557step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15558step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15558step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15559step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15559step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15560step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15561step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15561step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15561step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15561step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15561step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15562step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15562step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15563step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw15564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15564step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15565step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw15567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw15568step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw15568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw15569step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15569step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15569step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15569step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15570step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15570step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15570step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15571step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15571step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15571step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15571step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw15572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw15572step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15572step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw15572step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15572step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw15572step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw15582step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15583step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15586step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15592step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15594step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15595step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw15597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw15598step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw15599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15599step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15599step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15601step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw15602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw15602step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw15602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15603Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15603step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15603step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15604Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15604step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15605Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15605step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15605step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15606Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15606step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15607Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15607step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15607step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15608step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15608step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15609Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15609step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15609step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15609step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15611step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15611step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15611step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15611step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw15612step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15612step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15612step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15613Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15613step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15613step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15613step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15613step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15614Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15614step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15614step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15614step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15615Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15615step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15615step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15615step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15615step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15615step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15616step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15616step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15616step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15617Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15617step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15617step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15617step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15617step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15617step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15618step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15618step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15619Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15619step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15619step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15620step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15621step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15621step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15621step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15621step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15622step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15622step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15622step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15623step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15623step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15623step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15623step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15624step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15625step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15625step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15626step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw15627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15627step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw15628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw15628step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15628step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw15628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15629step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15631step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw15632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15632step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15633Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15633step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15634Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15634step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15635Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15635step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15635step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15635step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15636Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15636step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15636step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15637Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15637step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15637step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15638Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15638step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15639 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw15639Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15639step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw15639step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15639step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw15639step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15639step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw15639step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15640Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15640step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15641step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15642step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw15644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15645step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15647step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15650step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw15651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw15652step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15655Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15656Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15656step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15657step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15658Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15658step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15658step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15659Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15659step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15659step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15659step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw15660Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15660step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15660step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15660step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15661Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15661step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15661step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw15662Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15662step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15663step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15663step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15664 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15664step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15664step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15664step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15664step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15664step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15665 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15665step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15665step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15665step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15665step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15669step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15671 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw15671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15676 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15680 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15682 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15682step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15682step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15682step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15683 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15683step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15685 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15686 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15687 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15688 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15688step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15689 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15691 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15692 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15693 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15694 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw15694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15695step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15696 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15696step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15697 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15697step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15698 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15699 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw15699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15699step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15701 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15701step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15702 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15702Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15702step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15703 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15704 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw15704step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15706 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15707 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15707step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15707step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15708 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15708step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15708step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15709 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15709step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15710step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15711 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15711step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15712 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15712step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15713step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15713step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15714 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw15714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15715 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15715step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15715step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15715step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15716 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15716step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15716step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15716step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15717 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15717step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15717step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15717step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15718 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15718step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15718step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15718step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15719step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw15719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15719step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw15719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15720 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15720step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15720step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15721 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw15721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15721step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw15721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15722 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15722step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15722step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15723step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15723step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15723step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15723step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15723step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15724 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15724step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15724step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15726 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15726step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15726step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15726step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15726step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15727step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15727step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15727step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15727step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15728step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15728step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15729step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15729step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15730step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15730step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15731step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15731step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15732 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15732step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15733step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15733step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15734 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15734step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15735step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15735step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15736 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw15736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15736step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15737 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15738 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15739 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15740 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15741 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15742 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15744 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15745 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15746 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15746Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw15746step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15747 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw15747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15748 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15748step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15749 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15750 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15751 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15752 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15753 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15754 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw15754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15756 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15757 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw15791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw15791step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15791step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15795step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15796step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15796step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15798step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15799step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15799step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15800step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15800step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15801step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15802step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15802step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15804step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15804step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15805step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15805step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw15806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15806step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15807step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15808step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw15809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15809step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15809step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw15810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15810step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15811step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15811step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw15813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15814step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15815step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15815step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15816step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15817Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15817step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15818Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15819Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15820Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15821Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15822Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15823Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15823step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15825Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15826Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15828Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw15831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15832Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw15832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15833step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15834step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw15835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15835step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15836Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15836step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15837Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15837step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15837step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15838Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15838step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15838step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15839Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15839step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15839step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15839step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15840Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15840step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15840step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15841Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw15841step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15841step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15841step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15841step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15842Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw15842step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15842step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15842step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15842step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15843Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15843step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15843step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15844Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw15844step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15844step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15844step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15844step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15845Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15845step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15845step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15845step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15845step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15845step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15846Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw15846step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15846step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15846step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end


