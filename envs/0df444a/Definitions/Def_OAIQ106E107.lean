-- Prove2me | Definitions.Def_OAIQ106E107
-- name    : OAIQ106E107
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:16:27.283924+00:00
-- url     : https://prove2.me/theorems/db5fe642-cf1d-4d75-bb0e-b769d62cdc51
-- title:
--   Definitions bundle OAIQ106E107 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7310 declarations of OpenAI's Lean: 7310 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw32955Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32955step0`, `OAI.MUB6.Certificate.MixedSemantics.raw32955step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32955step1`, `OAI.MUB6.Certificate.MixedSemantics.raw32955step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32955step2`, `OAI.MUB6.Certificate.MixedSemantics.raw32955step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32956`, `OAI.MUB6.Certificate.MixedSemantics.raw32956Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32956step0`, `OAI.MUB6.Certificate.MixedSemantics.raw32956step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32956step1`, `OAI.MUB6.Certificate.MixedSemantics.raw32956step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32956step2`, `OAI.MUB6.Certificate.MixedSemantics.raw32956step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32957`, `OAI.MUB6.Certificate.MixedSemantics.raw32957Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32957step0`, `OAI.MUB6.Certificate.MixedSemantics.raw32957step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32957step1`, `OAI.MUB6.Certificate.MixedSemantics.raw32957step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32957step2`, `OAI.MUB6.Certificate.MixedSemantics.raw32957step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32958`, `OAI.MUB6.Certificate.MixedSemantics.raw32958Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32958step0`, `OAI.MUB6.Certificate.MixedSemantics.raw32958step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32958step1`, `OAI.MUB6.Certificate.MixedSemantics.raw32958step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32959`, `OAI.MUB6.Certificate.MixedSemantics.raw32959Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32959step0`, `OAI.MUB6.Certificate.MixedSemantics.raw32959step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32959step1`, `OAI.MUB6.Certificate.MixedSemantics.raw32959step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw3295Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw3295step0`, `OAI.MUB6.Certificate.MixedSemantics.raw3295step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw3295step1`, `OAI.MUB6.Certificate.MixedSemantics.raw3295step1Labels` and 7270 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical25`, `MutuallyUnbiased_MixedSemantics_Canonical257`, `MutuallyUnbiased_MixedSemantics_Canonical258`, `MutuallyUnbiased_MixedSemantics_Canonical259`, `MutuallyUnbiased_MixedSemantics_Canonical26`, `MutuallyUnbiased_MixedSemantics_Canonical260`, `MutuallyUnbiased_MixedSemantics_Canonical261`, `MutuallyUnbiased_MixedSemantics_Canonical262`, `MutuallyUnbiased_MixedSemantics_Canonical263`, `MutuallyUnbiased_MixedSemantics_Canonical264`, `MutuallyUnbiased_MixedSemantics_Canonical265`, `MutuallyUnbiased_MixedSemantics_Canonical266`, `MutuallyUnbiased_MixedSemantics_Canonical267`, `MutuallyUnbiased_Tao_TaoArithmetic`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106E155`; the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1170_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2986_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2987_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound26_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound36_e`.
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

def raw32Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw32step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw32step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 4, -2]]
def raw33Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw33step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw33step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw34 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]

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

def raw329Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw329step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw329step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw329step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw330 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 2, -2], ![-2, 2, 0]]
def raw330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw330step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw330step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw331 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 2, -2], ![-2, 2, 0]]
def raw331Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw331step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw331step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw332 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw332step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw332step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw333 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw333Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw333step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw333step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw336 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw336Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw336step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw336step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw336step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw337 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw337Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw337step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw338 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw338Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw338step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw339 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw339Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw339step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw340 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw340Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw340step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw340step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw341 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw341Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw341step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0]]
def raw3297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0]]
def raw3297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw3297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3297step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0]]
def raw3298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1]]
def raw3298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3298step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3298step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![1, 0, -1]]
def raw3298step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3298step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3298step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw3298step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3298step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3299step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0]]
def raw3302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0]]
def raw3302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3302step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0]]
def raw3303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw3303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3303step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0]]
def raw3307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0]]
def raw3307step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3307step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0]]
def raw3308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw3309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw3309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw3309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3309step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3309step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw3310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw3310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0]]
def raw3310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3310step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3310step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw3311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw3311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3311step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw3312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw3312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3312step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0]]
def raw3313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw3313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw3313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3313step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw3313step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3314step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3314step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3315step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3315step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw3315step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3315step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw3315step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3315step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw3315step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3316step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3316step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw3318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw3318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3318step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3319Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3319step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3319step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3319step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3319step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3319step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3320Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3320step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3320step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3320step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3320step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3320step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3321Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3321step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3321step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3321step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3321step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3321step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0]]
def raw3322Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3322step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3322step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3322step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3322step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3322step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -1, 0]]
def raw3322step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3322step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]
def raw3322step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3323Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3323step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3323step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3323step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw3323step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3324Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3324step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3324step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3324step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3324step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3324step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3325Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3325step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3325step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3325step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3325step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3325step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0]]
def raw3326Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3326step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3326step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3326step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3326step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3326step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3326step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3327Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3327step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3327step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3327step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw3327step2Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical257
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw32955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw32955step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw32955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32955step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw32955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw32956step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32956step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw32957step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32957step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32957step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32957step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw32958step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32958step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw32958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw32959step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw32959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw32960step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw32960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw32961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw32961step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw32961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw32961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32962Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32962step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw32965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw32966step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32966step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32966step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32966step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32966step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw32967step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32967step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32967step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32967step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32967step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw32968step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32968step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32968step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32968step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw32969step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32969step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32969step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32969step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32971step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32972step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32972step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32972step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32973step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32973step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32974step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32975step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32976step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32976step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32977step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32977step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32977step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32978step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32978step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32978step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32979step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32979step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32980step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32980step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32980step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32981step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32981step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32982step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32982step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32983step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32984step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32984step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32985step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32985step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32986step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32987step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32988step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32988step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32989step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32989step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw32990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32990step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw32991step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32991step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw32991step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw32992step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw32992step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32992step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw32992step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw32993step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw32993step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32993step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw32993step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw32994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw32994step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32994step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32994step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32994step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw32995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw32995step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32995step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32995step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32995step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32995step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32999 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32999step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32999step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32999step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32999step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32999step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33001 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33001step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33001step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33001step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33003 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw33003step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33003step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33003step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33003step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33003step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical258
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33050step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33055step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33056step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33057step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33058step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33059step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33060step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw33068step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw33068step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33068step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw33068step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw33069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33070step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33070step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33071Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33071step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33071step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33071step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33071step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33072step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33072step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33072step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33072step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33072step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33072step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33073Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33073step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33073step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33073step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33074Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33074step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33074step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33074step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33075Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33075step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33075step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33075step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33075step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33076Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33076step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33076step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33076step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33077Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33077step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33077step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33077step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33077step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33077step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33078Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33078step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33078step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33079Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw33079step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33079step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33079step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33080Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw33080step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33080step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33080step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33081Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw33081step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33081step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33081step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33081step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33082Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33082step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw33082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33082step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33082step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33082step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33083Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33083step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33083step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33083step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33083step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33084Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33084step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33084step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33085Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33085step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33085step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33085step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33086Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33086step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33086step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33086step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33087Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33087step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33087step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33087step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw33088step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33088step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33088step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw33089step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33089step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33089step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw33090step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw33090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw33091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33091step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw33091step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33091step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33091step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33091step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33136 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw33136step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33136step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33136step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33136step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33140 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw33140step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33140step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33140step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33140step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33142 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33142step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33142step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33145 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33145step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33145step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33145step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33146 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33146step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33146step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33147 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw33147step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33147step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33147step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33147step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33149 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33149Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw33149step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33149step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33150 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33150Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw33150step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33150step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33150step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33151 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33151Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw33151step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33151step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical259
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33152 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33152Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw33152step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33152step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33153 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33153Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw33153step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33154 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw33154Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw33154step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33154step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33162step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33163step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33165step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33166step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33167step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33171step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33175step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33176step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33177step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33177step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33178step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33178step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33178step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33179step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33179step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33179step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33179step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33179step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33179step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33180step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33180step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33180step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw33181step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33181step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33182step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33182step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33183step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33183step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33184step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33184step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33184step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33184step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33185step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33185step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33185step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33185step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33185step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw33186step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33186step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33186step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw33187step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33187step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw33188step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33188step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33188step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw33189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33189step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33189step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33189step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw33190step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33190step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33190step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33190step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw33191step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33191step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33191step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33191step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33191step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw33192step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33192step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33193step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw33193step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33193step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33193step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33193step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw33194step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33194step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw33195step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33195step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33195step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw33196step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw33196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw33196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33197step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw33197step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33197step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33197step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33197step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33198step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw33198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33198step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33198step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33198step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33233 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw33233step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33233step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33233step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33233step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33233step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33237 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw33237step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33237step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33237step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33237step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33241 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw33241step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33241step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33241step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33241step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33241step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

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

def raw3328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3328Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3328step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3328step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3328step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3329Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3329step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3329step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3329step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3329step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3329step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0]]
def raw3330Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3330step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3330step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3330step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3330step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3330step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3330step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3331Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3331step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3331step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3331step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw3331step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3332Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3332step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3332step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3332step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3333Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3333step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3333step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3333step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw3334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3334step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3334step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3334step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3334step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3334step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3334step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3335step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3335step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3335step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3335step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3335step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw3335step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3335step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw3335step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3336step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3336step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3336step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw3336step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3336step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw3336step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3337step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3337step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw3337step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3337step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw3337step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3338step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3338step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3338step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw3338step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3338step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw3338step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0]]
def raw3339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3339step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3339step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3339step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3339step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3339step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 2, 0], ![2, -2, 0]]
def raw3339step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3339step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw3339step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3340step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3340step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3340step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3340step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3340step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 2, 0], ![2, -2, 0]]
def raw3340step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3340step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw3340step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3341 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3341step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3341step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3341step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3342 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3342step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3342step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3342step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3342step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3342step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3343 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3343step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3343step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3343step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3343step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3343step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3344 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw3344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw3344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3344step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3344step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3344step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3344step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3344step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3345 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw3345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw3345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3345step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3345step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3345step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3345step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3346step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3347step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3347step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3347step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3347step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3347step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3348step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3348step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3348step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3348step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw3349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw3349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3349step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3349step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3349step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3349step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw3350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw3350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3350step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3350step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3350step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3350step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw3353step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3353step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3353step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3353step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw3354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw3354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw3355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw3355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw3358step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3358step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3358step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3358step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3358step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw3359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw3359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3359step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw3360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw3360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3360step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw3361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3361step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3361step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3361step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3361step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw3362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3362step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3362step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3362step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3362step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw3363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3363step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3363step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3363step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0]]
def raw3364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3364step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3364step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3364step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0]]
def raw3365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw3365step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3365step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3365step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3365step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw3366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3366step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3366step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3366step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3366step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3366step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw3367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3367step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3367step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3367step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3367step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw3368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3368step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3368step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw3369Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3369step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3369step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw3370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3370step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw3370step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3370step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3370step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3370step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3370step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3371 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3371step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3371step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3371step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3371step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3372 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3372Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3372step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3373 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3373step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3373step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3373step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3373step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3374 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3374step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3374step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3374step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3374step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3375 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3375step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3376step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3377step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3378step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3378step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3378step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3378step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3378step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3378step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3379step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3379step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3379step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3380step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3380step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3380step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3380step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3380step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3381step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3381step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3382step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3382step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3382step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3382step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3383step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3383step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3384step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3384step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3384step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3385step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3385step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3385step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3386step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3386step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3387step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3389step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3389step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3389step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3391step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3391step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3391step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3391step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw3392step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw3392step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3393step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3393step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3393step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3393step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3394step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1]]
def raw3395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3395step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3396step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3396step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3397step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3397step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3397step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3398step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3398step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3398step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3398step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw3399step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3399step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3399step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3399step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw3400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3400step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3400step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3400step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3401 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3401step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3401step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3402 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3402step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3402step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3402step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3403 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3403step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3403step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3403step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3403step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw3403step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3403step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3404 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3404step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3404step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3404step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3404step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3404step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3405 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3405step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3405step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3405step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3405step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3405step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3405step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3405step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3406step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3406step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3406step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3406step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw3407step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3407step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3407step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3408step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3408step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3408step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3409step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3409step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3409step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3410step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3410step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3410step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3410step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3411step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3411step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3412step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3412step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3413step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3414step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3415step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3416step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3416step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3416step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3416step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3417step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3417step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3418step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3419step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3419step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3419step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3420step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3420step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3421step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3421step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3422step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3422step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3423step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3424step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3424step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3424step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3424step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical260
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw33302step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw33302step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33303step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33303step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33303step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw33304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33304step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33304step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33304step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33304step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw33305step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33305step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw33305step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33307step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw33308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw33312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33314step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33315step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33316step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw33317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33317step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw33317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw33318step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33320step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw33322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw33322step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw33322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw33323step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33323step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw33323step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33323step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33323step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33324step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw33324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw33324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33325Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33325step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw33326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33326step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33326step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33326step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33326step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33326step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33326step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33327Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33327step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33327step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33328step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw33328step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw33328step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33329Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33329step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33329step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw33330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33330step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33330step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33330step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33330step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33330step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33330step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33331Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33331step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33331step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw33332step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw33332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33333Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw33333step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33333step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw33333step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw33334Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33334step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33334step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33334step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33335Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33335step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33335step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33336Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33336step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw33336step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw33336step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33337Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33337step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw33337step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33337step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw33337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33338Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33338step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw33339Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33339step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw33339step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33339step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw33339step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33339step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw33339step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33340Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33340step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33340step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33341Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33341step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw33341step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw33341step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33342Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33342step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw33342step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33342step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw33342step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33343Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33343step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33343step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw33344Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw33344step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33344step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33344step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33344step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33345Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33345step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw33345step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33345step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33345step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33345step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33345step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical261
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33420 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33420step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw33420step1Labels : Fin 2 → Fin 3 := ![1, 2]

def raw33420step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw33420step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw33420step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw33420step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw33458 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33458step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33458step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33458step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33458step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, 0, 2]]
def raw33472step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33472step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33472step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33472step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33473step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33473step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33473step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33474step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33474step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33474step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33474step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33474step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33475step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33475step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33475step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33475step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33475step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33484step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw33486step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33486step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33486step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33486step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw33487step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33487step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33487step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33487step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33488step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw33488step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33488step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33488step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33488step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33489Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33489step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, 0, 2]]
def raw33489step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33489step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33489step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33489step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33489step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33490Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33490step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33490step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33490step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33491Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33491step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33491step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33491step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33491step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33491step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33491step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33492Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33492step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33492step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33492step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33492step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33492step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33492step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33493Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33493step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33493step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33493step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33493step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33493step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33493step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33494Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33494step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33494step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33494step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33494step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33494step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33494step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33495Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]
def raw33495step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw33495step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33495step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw33495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33496step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33496step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33497Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33497step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33497step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33497step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33498step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33498step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33498step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33499step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw33499step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33499step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33499step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33499step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33499step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33500step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33500step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33500step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33501Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33501step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw33501step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33501step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33501step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33501step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33501step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33502step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33502step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33502step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33502step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33503Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33503step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw33503step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33503step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33503step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33503step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33504step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33504step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33504step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33505Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33505step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw33505step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33505step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33505step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33505step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw33506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw33506step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33506step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33506step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33506step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33506step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33506step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33507Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33507step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw33507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw33507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw33508step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw33508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33509step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw33509step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw33509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33510step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw33510step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33510step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw33510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33511step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw33511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw33511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33516step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33516step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33516step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33517step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33517step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33518step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33518step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33519step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33519step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33520step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33520step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33521step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33521step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33522step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw33523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33523step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33523step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33523step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33524step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33524step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33524step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33525step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33525step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33526step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw33527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33527step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33527step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33527step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33528Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33528step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33529Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33530Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33530step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw33530step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33531Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33531step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33532Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33532step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33533Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw33534step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw33534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical262
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33538step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33540step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33541step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33542Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33543Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33543step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw33543step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33543step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33544Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33544step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33545Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33545step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw33545step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33546Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33546step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33547Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33547step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33548Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33549Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33549step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw33549step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33549step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33553 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33553step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33553step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33553step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33553step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33556 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33556step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33556step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw33558step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33558step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33558step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33558step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33558step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33559 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw33559step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33559step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33559step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33559step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33559step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33560 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33560step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33560step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33560step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33561 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw33561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw33561step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33561step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33561step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33561step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33566step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33566step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33566step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33566step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33567 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33567step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33567step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33568 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33568step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33568step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw33569step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33569step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33569step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33569step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33570step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33570step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33570step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw33571step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33571step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33571step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33571step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33572step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33572step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33572step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33572step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33572step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33573step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33573step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33573step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33573step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33573step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33574step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw33576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33579step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33589step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw33590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33591Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33591step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw33591step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33591step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33591step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33591step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33592Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33592step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33592step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33592step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33593Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33593step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw33593step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33593step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33593step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33593step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33594Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33594step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33594step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33594step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33594step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33594step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33594step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33594step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33594step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33595Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33595step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33595step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33595step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33595step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33595step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33596Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33596step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33596step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33596step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33596step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33596step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33597Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw33597step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33597step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33597step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33597step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33598Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw33598step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33598step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33598step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33599Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33599step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33599step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33599step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33599step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33599step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33600step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33600step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33600step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33600step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33601Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33601step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw33601step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33601step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw33601step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33601step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw33601step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33602Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw33602step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33602step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33602step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33603Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33603step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33603step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw33603step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33603step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33603step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33603step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33603step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33604Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33604step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33604step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33604step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33604step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33604step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33605Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33605step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw33605step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33605step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33605step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33605step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33606Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33606step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33606step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33606step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33607Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33607step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw33607step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33607step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33607step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33607step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33608step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33608step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33608step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33608step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33609Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33609step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3]]
def raw33609step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw33609step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33609step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw33609step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw33610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw33610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw33610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33611step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw33611step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw33611step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33611step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw33611step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw33612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33612step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33612step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33612step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw33612step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33612step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw33612step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33612step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw33612step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33613Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33613step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw33613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw33613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33614step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33615Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33615step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33616step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33616step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33617step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33617step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33618step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33618step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33618step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33618step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33619step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33619step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33620step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33620step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33621step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33622step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33622step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw33623step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw33623step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33623step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw33623step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33624step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33624step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33625step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33625step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33626step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33626step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33627step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33627step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw33628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw33628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw33628step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33628step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33628step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33628step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33628step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33630step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33632step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33635step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw33636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33640step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw33641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw33641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw33641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33642step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw33642step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33642step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33642step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33642step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33643 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw33643step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33643step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33643step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33643step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33644 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw33644step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33644step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw33644step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33645 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33645step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw33645step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33645step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33645step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33645step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33646step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33646step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33646step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33646step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33647 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33647step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33648step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw33648step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33648step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33648step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33648step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33649 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33649step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33649step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33649step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33650 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw33650step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33650step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33650step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33650step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33651 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw33651step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33651step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33651step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33651step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33652step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33652step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33652step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33652step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33653step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, 0, 2]]
def raw33654step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33654step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33654step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33654step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33655step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33655step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33655step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33656step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33656step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33656step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33656step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33656step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw33657step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw33657step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33657step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw33657step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33661step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical263
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw33667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw33667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33670step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33671Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33671step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw33671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw33671step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw33672step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33673Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33673step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33673step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw33673step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33673step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw33673step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33674Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33674step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33674step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33674step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw33674step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33674step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw33674step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33675Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33675step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw33675step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33675step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33676Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33676step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33677Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33677step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33677step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33678step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33680step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33682step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw33682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33683step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33684step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33686step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw33686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw33687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw33687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -1, 3], ![-3, 3, 0]]
def raw33688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw33688step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw33689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33689step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33690step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, -1, 2], ![-3, 3, 0]]
def raw33690step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw33690step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33691Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33691step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, 0, 2]]
def raw33691step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33691step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33691step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33691step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33692Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33692step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33692step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33692step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33692step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33693Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33693step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33693step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33693step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33693step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33693step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33693step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33693step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33694Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33694step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33694step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33694step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33694step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33694step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33694step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33694step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33695Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33695step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw33695step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw33695step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33695step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw33695step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33696Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, 0, 2]]
def raw33696step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33696step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33696step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33696step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33697Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33697step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33697step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33697step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33697step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33697step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33698Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33698step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33698step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33698step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33698step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33698step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33699Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw33699step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33699step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw33699step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33699step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw33699step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33700Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33700step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw33700step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw33700step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33700step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw33700step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33701Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw33701step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33701step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33702step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33702step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33702step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw33702step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33702step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33702step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33702step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33702step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33703step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw33703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw33703step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33703step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw33703step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33704step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw33704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw33704step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33704step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw33704step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw33705step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33705step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33705step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33706step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw33706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33706step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33706step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33706step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33706step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw33707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw33707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw33707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw33707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33707step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw33707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33708step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, -1, 3]]
def raw33708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw33708step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33708step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw33708step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw33709step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw33709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33709step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw33709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33710step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw33710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33710step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw33710step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33710step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw33710step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33711Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33711step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw33711step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33711step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33712Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33713Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33713step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33713step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33714Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33715Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33715step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33716Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33716step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33717Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33717step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33718Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw33719step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33719step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33719step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33719step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw33720step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33720step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33720step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33720step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33720step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw33721step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33721step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33721step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33721step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33722step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33723step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33723step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33724step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33724step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33724step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33724step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33725step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33725step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33726step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33726step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33727step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33727step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33728step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw33728step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw33728step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33728step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw33728step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33729step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33729step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33730step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33730step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33730step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33731step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33731step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33732step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33732step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33732step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33733Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33733step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33733step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33733step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33734step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33734step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33735step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw33735step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw33735step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33735step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw33735step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33736Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33736step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33737Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33738Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33738step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33739Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33739step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33740Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33740step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33741Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33741step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33742Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33743Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33743step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33744Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33744step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33745Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33745step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33746Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33746step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33747Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33748Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33749Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33750Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33751Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33751step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33752Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33752step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33753Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33754Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33754step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw33754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33755Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33755step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33756Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33756step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33757Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33757step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33758Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33759Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33759step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw33759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw33760Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw33760step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33761Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33761step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33762Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33762step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33763Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33764Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33764step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw33764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw33764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33765Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33765step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw33765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw33765step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33766 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33766step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33766step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw33767step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw33767step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw33767step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33768 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw33768step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw33768step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33768step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw33768step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33769 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw33769step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw33769step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33769step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw33769step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33770 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw33770step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw33770step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33770step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw33770step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33771step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33771step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33771step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33771step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33771step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33772 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33772step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33772step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33772step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33772step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33773 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33773step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33773step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33773step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33773step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33774step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33774step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33774step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33774step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33775 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33775step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33776 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33776step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33776step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33776step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33776step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33777 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33777step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33777step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33777step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33777step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw33778step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33778step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw33778step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33778step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw33778step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33779 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33779step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33780 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw33780step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33780step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw33780step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33780step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw33780step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33781 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw33781step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw33781step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33781step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw33781step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33782 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw33782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw33782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw33782step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw33782step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33782step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw33782step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33784Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33784step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33788Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33791step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33791step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33791step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33791step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical264
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33792step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33792step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33792step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33792step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw33793step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33793step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33793step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33793step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw33794step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33794step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33794step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33794step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33795step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33795step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33795step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33795step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33801step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33802step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33804step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33805step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw33809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw33812step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33812step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33812step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33812step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33813Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33813step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33813step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33813step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33813step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33814step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33814step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33814step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw33815step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33815step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33815step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33815step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw33816step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33816step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33816step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33817step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33817step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33817step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33817step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33818step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33818step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33818step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33818step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33818step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33819step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33819step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33819step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33819step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33819step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33820Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33820step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33820step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33820step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33820step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33820step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33821Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33821step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33821step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33821step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33821step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33821step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33822Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33822step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33822step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33822step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33822step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33823Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33823step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33823step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33823step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33823step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33824Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33824step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33824step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33824step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33824step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33824step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33825Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33825step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33825step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33825step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33825step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33826Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33826step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33826step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33826step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33826step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33827Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33827step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33827step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33827step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33827step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33828Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33828step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33828step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33828step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33828step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33829Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33829step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33829step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33829step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33829step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33830Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33830step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33830step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33830step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33830step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33831Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33831step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33831step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33831step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33831step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33831step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33832Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33832step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33832step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33832step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33833Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33833step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33833step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33833step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33834Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33834step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33834step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33834step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33834step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw33835Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33835step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33835step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33835step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33835step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33836Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33836step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33836step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33836step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33837Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33837step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33837step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33837step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33837step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33838Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw33838step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw33838step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33845step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33845step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33845step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw33846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw33847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33847step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33847step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33848step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33848step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33848step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33849step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33849step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33850step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33850step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33851step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33851step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33851step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33852step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33853step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33854step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33854step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33855step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw33856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33856step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33856step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33857step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33858step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33859step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33859step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33860step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33860step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw33861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33861step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33861step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33863 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw33863step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33863step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33863step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33864 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33864step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw33866step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33866step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33866step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33866step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33867 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33867step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33868 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33868step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33869 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw33869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33869step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33869step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33871 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw33871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33871step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33871step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33873step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33873step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33873step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33873step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33874step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33874step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33874step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33874step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33875step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33875step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33875step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33875step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33876step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33876step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33876step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33876step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33876step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33877step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33877step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33877step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33877step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33878step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33878step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33878step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33878step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33878step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33880step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33883step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw33903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33904Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33905Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw33905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33906Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33907Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33907step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33908Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw33908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33909step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33909step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33910step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33911step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33912step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33912step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw33912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33913step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33917step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw33917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical265
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33922step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw33922step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw33927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw33930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33930step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw33930step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw33931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33931step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw33932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33932step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw33933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33933step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw33933step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33933step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33933step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33934Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33934step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33934step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33934step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33934step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33935Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33935step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33935step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33935step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33935step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33935step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33936Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33936step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33936step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33936step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33936step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33936step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33937Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33937step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33937step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33937step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33937step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33937step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33938Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33938step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33938step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33938step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33938step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33939Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33939step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33939step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33939step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33939step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33939step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33940step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33940step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33940step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33940step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33940step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33941step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33941step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33941step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33941step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33941step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33942step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33942step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33942step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33942step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33942step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33942step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33943step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33943step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33943step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33944step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33944step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33945step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33945step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33945step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33945step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33946step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33946step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33947step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33947step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33947step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33947step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33947step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33948step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33948step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33948step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw33949step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33949step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33949step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw33950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33950step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw33951step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33951step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33951step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33951step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33952step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw33952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33952step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33952step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33952step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33953step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33953step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33953step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33954step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33954step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33954step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33955step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33955step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33956step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33956step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33957step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33957step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33957step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33957step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33958step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33958step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33958step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw33959step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33959step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33959step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw33960step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33960step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33960step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw33961step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33961step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw33961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33961step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw33961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw33962step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33962step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33962step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw33963Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33963step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw33963step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33963step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33963step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33963step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33970step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33970step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33970step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33971step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33972step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33972step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33972step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33973step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33973step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33973step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33974step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33975step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33976step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33976step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33977step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33977step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33977step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33978step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33979step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33979step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33980step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33980step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33980step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33981step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33981step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33982step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33982step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw33983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33983step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw33984step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33984step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33984step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33985 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33985step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33985step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw33986step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33986step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33986step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33986step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33987 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33987step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw33988step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33988step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33988step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33988step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33989step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33989step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33989step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33989step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33990step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33990step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33990step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33990step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33991step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33991step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33991step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33992step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33992step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33992step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33992step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw33993step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33993step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33993step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33993step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33995step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33996step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33997step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33997step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw33998step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33998step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33998step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33998step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34001step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34001step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34002step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34006step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34008step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw34018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34019Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34019step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34019step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34020Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34020step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34021Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34021step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34021step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34022Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34022step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34022step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34023Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34024Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34024step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34025Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34025step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34026Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34026step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34026step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34026step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw34026step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34027Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34027step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34027step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw34027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34028Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34028step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34029Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34030Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34031Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34031step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34032Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34032step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34033Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34034Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34035Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34036Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34037Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34037step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw34037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34038Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34042Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34042step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw34042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34044Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34045Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw34045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw34045step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34046Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw34046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw34046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34047Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34047step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw34047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34047step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical266
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw34048Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34048step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw34048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34048step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34049Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34049step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34049step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34049step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34050Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw34050step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34050step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34050step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34050step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34051Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34051step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34051step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34051step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34051step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34051step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34052Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34052step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34052step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34052step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34052step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34053Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw34053step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34053step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34053step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34053step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34054Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34054step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34054step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34054step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34054step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34054step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34055Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34055step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw34055step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34055step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34055step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34055step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34056Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34056step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34056step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34056step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34056step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34056step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34056step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34056step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34056step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34057Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34057step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34057step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34057step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34057step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34057step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34057step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34057step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34057step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34057step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34058Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34058step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw34058step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34058step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34058step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34058step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34058step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34059Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34059step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34059step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34059step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34059step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34059step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34060Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34060step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34060step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34060step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34061Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34061step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34061step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34061step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34061step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34061step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34062Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34062step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34062step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34062step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34062step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34062step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34063Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34063step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34063step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34063step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34064Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34064step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34064step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34064step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34065Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34065step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34065step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34065step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34065step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34066Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw34066step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34066step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34066step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34067Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34067step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34067step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34067step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34067step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34067step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34067step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34068Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34068step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34068step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34068step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34068step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34069Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34069step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34069step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34069step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34070step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34070step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34071Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw34071step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34071step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34071step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34071step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34072step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34072step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34072step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34072step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34072step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34072step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34073Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34073step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34073step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34073step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34074Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw34074step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34074step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34074step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34075Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw34075step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34075step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34075step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34075step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34076Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw34076step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw34076step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34076step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw34076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34077Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34077step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw34077step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34077step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34077step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34077step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw34078Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34078step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw34078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34078step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34078step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34078step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34079step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34080step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34080step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw34081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw34081step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34081step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34081step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34081step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34082step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34082step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34083step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34083step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw34084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw34084step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34084step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34084step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34084step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34085step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34086step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34087step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw34088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34088step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw34089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34089step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34089step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw34090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34090step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw34091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34091step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34092step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34093step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34093step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34094step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34094step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw34095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw34095step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw34095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34096step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34096step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34096step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34096step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34097 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34097step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34098 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw34098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34098step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw34099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw34099step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34099step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34099step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34099step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34099step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34100 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw34100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34100step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw34101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw34101step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34101step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34101step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34101step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34101step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34102 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw34102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw34102step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw34102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34103 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw34103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw34103step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34103step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw34103step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34104step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34104step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34104step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34104step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34105step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34105step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34105step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34105step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34106step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34106step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34106step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34106step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34107step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34107step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34107step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34107step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34107step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34108step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34108step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34108step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34108step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34109step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34112step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34114step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34116step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34116step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34117step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34117step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34118step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34119step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34120step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34121step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw34122step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw34123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw34125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw34125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw34125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34126Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34126step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34126step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34126step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34126step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34126step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34127Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34127step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34127step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34127step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34127step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34128Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34128step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34128step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34128step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34128step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34128step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34129Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34129step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34129step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34129step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34129step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34129step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34130Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34130step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34130step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34130step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34130step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34130step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34131Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34131step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34131step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34131step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34131step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34131step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34131step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34131step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34131step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34132Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34132step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34132step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34132step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34132step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34133Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34133step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34133step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34133step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34133step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34134Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34134step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34134step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34134step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34134step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34135Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34135step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34135step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34135step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34135step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34135step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34136Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34136step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw34136step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34136step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34136step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34136step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34137Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw34137step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34137step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34137step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34137step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34138Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34138step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34138step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34138step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34138step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34138step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34139Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34139step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34139step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34139step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34139step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34139step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34140Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34140step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw34140step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34140step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34140step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34140step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34141Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw34141step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34141step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34141step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34141step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34142Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34142step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw34142step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw34142step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34142step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw34142step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34143Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34143step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34143step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34143step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34143step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34143step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34144Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34144step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw34144step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw34144step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34144step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw34144step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34145Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw34145step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34145step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw34145step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34145step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw34145step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34146Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34146step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw34146step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw34146step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw34147Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw34147step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw34147step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw34147step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34147step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw34147step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34148Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34148step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34148step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34149Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34149step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34149step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34150Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34150step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34151Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34151step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34151step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34152Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34152step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34153Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34153step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw34153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34154 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1], ![0, 0]]
def raw34154Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34154step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw34154step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34154step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]
def raw34154step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34154step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw34154step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34154step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw34154step3Labels : Fin 2 → Fin 2 := ![0, 1]

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

def raw34185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw34185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw34185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw34185step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34185step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34185step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34185step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34186 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw34186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw34186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw34186step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34186step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34186step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34186step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34187 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw34187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw34187step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34187step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34187step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34187step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34188 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw34188step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw34188step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34189 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw34189step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw34189step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw34190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw34190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw34190step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34190step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34190step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34190step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34191 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw34191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw34191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw34191step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34191step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34191step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34191step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34192 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw34192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw34192step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34192step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34192step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34192step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34193 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw34193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw34193step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw34193step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw34193step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34194step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34194step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34194step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34194step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34195 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34195step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34195step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34195step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34195step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34196step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34196step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34196step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34196step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34196step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34196step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34197step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34197step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34197step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34197step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34198step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34198step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34198step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34198step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34199step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34199step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34199step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34199step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34199step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34199step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34199step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34200step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34200step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34200step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34201step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34201step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34204step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34206step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34206step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw34208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34208step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw34208step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34208step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34208step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34209step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34213step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw34217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34218Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34218step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34218step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34218step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34218step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34218step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34219Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34219step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34219step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34219step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34219step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34220step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34220step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34220step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34220step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34220step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34221Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34221step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34221step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34221step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34221step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34221step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34221step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34221step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34222step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34222step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34222step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34222step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34222step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34223Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34223step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34223step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34223step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34223step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34223step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34223step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34223step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34223step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34223step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34224Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34224step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34224step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34224step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34224step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34225Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34225step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34225step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34225step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34225step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34225step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34226Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34226step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34226step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34226step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34226step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34226step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34226step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34227Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34227step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34227step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34227step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34227step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34227step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34228Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34228step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34228step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34228step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34228step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34228step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34228step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34229Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34229step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34229step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34229step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34229step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34229step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34230Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw34230step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw34230step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34230step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34230step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34230step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34230step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34230step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34230step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34231Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34231step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34231step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34231step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34231step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34231step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34232Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34232step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw34232step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34232step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34232step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34232step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34233Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw34233step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34233step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34233step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34233step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34233step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34234Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34234step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw34234step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw34234step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34234step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw34234step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34235Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34235step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34235step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34235step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34235step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34235step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34236Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34236step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw34236step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34236step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw34236step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34236step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw34236step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34237Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw34237step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34237step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw34237step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34237step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw34237step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34238Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34238step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw34238step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34238step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw34238step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34238step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw34238step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw34239Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34239step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34239step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34239step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw34239step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34239step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw34239step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34239step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw34239step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34240Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34240step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34241Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34241step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34242Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34242step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34242step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34243step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34243step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34244step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34244step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw34245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw34245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw34245step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34245step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34245step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34245step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw34246step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34246step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34246step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34246step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34247step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34248step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw34249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34249step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34250step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw34251step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw34251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw34252step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw34252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw34253step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_TaoArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arithmetic in `ℤ[ω]`, interpreted in the same complex root as Tao's
matrix.  These definitions are for certificate checking, not assumptions. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6.TaoArithmetic

abbrev Coeff := ℤ × ℤ

end MUB6.TaoArithmetic

end

end OAI
end


