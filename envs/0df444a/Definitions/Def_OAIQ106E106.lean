-- Prove2me | Definitions.Def_OAIQ106E106
-- name    : OAIQ106E106
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:16:25.376954+00:00
-- url     : https://prove2.me/theorems/be8d9fbf-3a46-4bd7-b579-8441b99237ef
-- title:
--   Definitions bundle OAIQ106E106 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7381 declarations of OpenAI's Lean: 7381 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw31632`, `OAI.MUB6.Certificate.MixedSemantics.raw31632Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31632step0`, `OAI.MUB6.Certificate.MixedSemantics.raw31632step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31633`, `OAI.MUB6.Certificate.MixedSemantics.raw31633Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31633step0`, `OAI.MUB6.Certificate.MixedSemantics.raw31633step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31634`, `OAI.MUB6.Certificate.MixedSemantics.raw31634Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31634step0`, `OAI.MUB6.Certificate.MixedSemantics.raw31634step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31634step1`, `OAI.MUB6.Certificate.MixedSemantics.raw31634step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31635`, `OAI.MUB6.Certificate.MixedSemantics.raw31635Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31635step0`, `OAI.MUB6.Certificate.MixedSemantics.raw31635step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31635step1`, `OAI.MUB6.Certificate.MixedSemantics.raw31635step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31636`, `OAI.MUB6.Certificate.MixedSemantics.raw31636Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31636step0`, `OAI.MUB6.Certificate.MixedSemantics.raw31636step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31637`, `OAI.MUB6.Certificate.MixedSemantics.raw31637Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31637step0`, `OAI.MUB6.Certificate.MixedSemantics.raw31637step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31638`, `OAI.MUB6.Certificate.MixedSemantics.raw31638Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31638step0`, `OAI.MUB6.Certificate.MixedSemantics.raw31638step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31638step1`, `OAI.MUB6.Certificate.MixedSemantics.raw31638step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31639`, `OAI.MUB6.Certificate.MixedSemantics.raw31639Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31639step0`, `OAI.MUB6.Certificate.MixedSemantics.raw31639step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31639step1`, `OAI.MUB6.Certificate.MixedSemantics.raw31639step1Labels` and 7341 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical24`, `MutuallyUnbiased_MixedSemantics_Canonical247`, `MutuallyUnbiased_MixedSemantics_Canonical248`, `MutuallyUnbiased_MixedSemantics_Canonical249`, `MutuallyUnbiased_MixedSemantics_Canonical25`, `MutuallyUnbiased_MixedSemantics_Canonical250`, `MutuallyUnbiased_MixedSemantics_Canonical251`, `MutuallyUnbiased_MixedSemantics_Canonical252`, `MutuallyUnbiased_MixedSemantics_Canonical253`, `MutuallyUnbiased_MixedSemantics_Canonical254`, `MutuallyUnbiased_MixedSemantics_Canonical255`, `MutuallyUnbiased_MixedSemantics_Canonical256`, `MutuallyUnbiased_MixedSemantics_Canonical257`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound2958_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2959_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2960_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2961_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound129_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound50_e`.
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

def raw31Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw31step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw32 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 4, -2]]

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

def raw316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw316step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw317 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw317Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw317step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw318 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw319 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw319Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw319step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw320 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw320step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw321 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw321Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw321step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw322 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw322step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw323 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw323Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw323step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw324 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw324step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw325 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw325Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw325step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw326 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 3, -2]]
def raw326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw326step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw326step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw327 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 3, -2]]
def raw327Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw327step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw327step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw328 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 3, -3]]
def raw328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw328step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw328step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw328step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw329 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 3, -3]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3163step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3164step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3167step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3167step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3167step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw3169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3171step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw3172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1]]
def raw3173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1]]
def raw3173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw3173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw3173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3175step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw3178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw3178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3178step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3178step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3179 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3179step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw3179step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3179step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3179step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3180 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3180step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3180step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3181 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3181step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3181step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3181step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3181step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3181step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3182 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1]]
def raw3182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1]]
def raw3182step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3182step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3182step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3183 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3183step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3183step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3183step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3184 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3184step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3184step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3184step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3184step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3184step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3184step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3185 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3185step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3185step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3186 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3186step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3186step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 0, 1], ![0, -1, 1]]
def raw3186step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3186step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3186step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3186step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3186step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3187 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1]]
def raw3187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1]]
def raw3187step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1]]
def raw3187step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3187step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3188 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3188step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3188step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3188step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3188step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3188step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3189 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3189step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3189step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3189step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3189step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3190 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3190step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3190step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3190step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3191 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3191step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3191step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3192 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1]]
def raw3192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3192step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3192step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3193 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3193step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3194 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw3194step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3194step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3194step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3194step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3195 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw3195step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw3195step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3196 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3196step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3196step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3197 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1]]
def raw3197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1]]
def raw3197step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3197step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3197step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3198 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3198step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3198step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3198step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3198step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3199 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3199step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3199step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3199step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3199step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical247
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw31632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw31634step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31637step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31638step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw31638step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31639step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31639step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw31639step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31640step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw31640step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw31640step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw31641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31641step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw31641step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31642step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31642step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw31642step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31643step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31644step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31644step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31644step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31644step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31644step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31645step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31645step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31645step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31645step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31645step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31646step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw31646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw31647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw31647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw31648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw31648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31649step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw31649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31650step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw31650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31651step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31651step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 1, -3], ![2, -2, 0]]
def raw31651step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31651step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw31651step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw31652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw31653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31654step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw31654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31655step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw31655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31656step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw31656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw31657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31658step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw31658step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31659step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw31659step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31660step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, 0, -2], ![3, -3, 0]]
def raw31660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31662step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31663step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31663step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -3, 0]]
def raw31663step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31664step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw31664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31664step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31664step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31665step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31665step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31665step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31666step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31666step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31667Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31667step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31667step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw31667step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31667step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw31667step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31668Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31668step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31668step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31668step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31669Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31669step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31669step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31670Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31670step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31670step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31670step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw31670step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31670step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw31670step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31670step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw31670step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31671Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31671step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31671step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31671step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw31671step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31671step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw31671step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31672Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31672step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31672step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31672step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 1, -3], ![2, -2, 0]]
def raw31672step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31672step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw31672step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31672step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw31672step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31672step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw31672step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31673Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31673step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw31673step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw31673step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31673step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw31673step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31674Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw31674step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw31674step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31674step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw31674step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31675Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31675step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw31675step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw31675step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31675step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw31675step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31676Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31676step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw31676step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31676step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31676step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31676step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31677Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31677step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw31677step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw31677step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31677step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw31677step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31678Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw31678step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31678step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw31678step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31678step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw31678step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31679Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31679step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw31679step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw31679step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31679step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw31679step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31680Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31680step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw31680step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31680step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31680step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31680step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31681Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31681step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31681step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31681step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw31681step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31681step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw31681step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31682Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31682step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw31682step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw31682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31683Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31683step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw31683step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw31683step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31684Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31684step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31684step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw31684step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31684step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw31684step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31685Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31685step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31685step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-3, 1, 2]]
def raw31685step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31685step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def raw31685step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31685step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def raw31685step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31686Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31686step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw31686step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw31686step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31686step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw31686step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31687Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31687step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw31687step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw31687step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31687step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw31687step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw31688Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw31688step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31688step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw31688step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31688step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-3, 2, 1]]
def raw31688step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31688step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw31688step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31688step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw31688step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31689step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31689step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw31692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31728step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31728step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw31728step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw31728step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31728step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw31728step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31729step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31729step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31729step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31730step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31730step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31730step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31730step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31730step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31731step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31731step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31731step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31731step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31731step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31731step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31731step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31732step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31732step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31733Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31733step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31734step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31734step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31735step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31735step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31737step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31737step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31738step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31738step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31738step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31738step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31738step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31739step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31740step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31740step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw31741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw31741step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![3, -1, -2], ![1, 0, -1]]
def raw31741step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31741step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw31741step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31742step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31742step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31742step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31743step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical248
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw31744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31745step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw31745step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31745step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw31745step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31745step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw31745step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31746step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31746step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31746step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31747step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31747step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31748step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw31748step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31748step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw31748step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31748step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw31748step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31749step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31749step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31749step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31749step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31749step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31749step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31749step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31750step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31750step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31750step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31750step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31750step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31751step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31751step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw31752step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31752step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31752step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31752step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31753step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31753step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31753step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31753step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31753step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31754Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31754step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31754step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31754step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31754step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31754step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31755Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31755step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31755step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31755step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31755step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31756step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw31756step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31756step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31756step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31756step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31757step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31757step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31757step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31757step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31757step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31758Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31758step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31758step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -1, 2], ![-2, -1, 3]]
def raw31758step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31758step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw31758step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31758step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw31758step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31759Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31759step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw31759step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw31759step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31759step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw31759step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31760Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31760step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw31760step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw31760step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31760step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw31760step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw31761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw31761step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![3, -1, -2], ![1, 0, -1]]
def raw31761step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw31761step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31761step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw31761step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31761step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw31761step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31762Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31762step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31762step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw31762step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31762step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw31762step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31762step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw31762step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31763Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31763step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw31763step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw31763step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31763step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw31763step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31764Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31764step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw31764step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw31764step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31764step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw31764step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31765step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31766step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31766step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31769step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31769step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31769step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31807step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31807step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31807step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31807step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31807step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31808step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31808step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31808step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31808step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31809step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31809step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31809step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31809step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31809step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw31810step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31810step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31810step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31810step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1]]
def raw31811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw31811step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31811step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31811step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31811step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31813step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31813step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31813step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31813step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31813step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw31815step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31815step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31815step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31815step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1]]
def raw31816step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw31816step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31816step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31816step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31816step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31817step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![1, 0, -1]]
def raw31821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31821step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw31821step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw31821step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw31821step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw31821step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw31821step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2], ![2, -1, -1]]
def raw31827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![3, -1, -2], ![2, -1, -1]]
def raw31828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![3, -1, -2], ![2, -1, -1]]
def raw31829step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31829step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw31831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2], ![1, 0, -1]]
def raw31831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw31831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw31836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw31836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![2, -2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw31867step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31867step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31867step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31867step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31868 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![2, -2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31868step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw31868step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31868step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31868step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31868step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31868step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31869 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw31869step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31869step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31869step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31869step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31870step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31870step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31870step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31870step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31871 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31871step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31871step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31871step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31871step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw31872 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31872step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31872step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw31873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw31873step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw31873step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw31873step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31873step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw31873step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31874 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw31874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw31874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw31874step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw31874step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31874step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw31874step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31875 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw31875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw31875step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw31875step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31875step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw31875step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw31876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw31876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw31876step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31876step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw31876step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31876step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw31876step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw31877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw31877step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31877step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw31877step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw31878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31878step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2], ![2, -2]]
def raw31878step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31878step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw31878step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw31879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw31879step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31879step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw31879step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31879step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw31879step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw31880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw31880step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31880step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw31880step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw31881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31881step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw31881step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw31882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw31882step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![3, -3, 0], ![2, -2, 0]]
def raw31882step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31882step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![3, -3], ![2, -2]]
def raw31882step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31882step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]
def raw31882step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw31883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw31883step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31883step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![3, -3], ![2, -2]]
def raw31883step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31883step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw31883step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31883step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw31883step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw31884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw31884step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31884step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![3, -3], ![2, -2]]
def raw31884step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31884step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw31884step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31884step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw31884step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, -1, 0]]
def raw31885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![1, -1, 0]]
def raw31885step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31885step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![3, -3, 0], ![1, -1, 0]]
def raw31885step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31885step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![3, -3], ![1, -1]]
def raw31885step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31885step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw31885step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw31887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw31887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw31888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw31889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw31893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw31894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31895 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw31895Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31895step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw31895step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31895step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw31895step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31895step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw31895step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31902 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![0, 0], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw31902Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31902step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw31902step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31902step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw31902step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw31906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw31907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31914 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw31914Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31914step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw31914step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31914step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw31914step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31921step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31927 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]
def raw31927Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31927step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw31927step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31927step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw31927step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31927step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw31927step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31928step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31929step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw31932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw31933Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw31933step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw31933step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31933step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31933step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31934 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![2, -2]]
def raw31934Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31934step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw31934step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31934step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw31934step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31934step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw31934step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31936step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw31937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw31937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw31938Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw31938step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31939Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31939step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31940Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31941Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31942Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31942step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31944Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw31944step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31945 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw31945Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31945step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw31945step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw31946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31946step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw31947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw31948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw31948step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw31949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw31949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31950Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31950step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31951step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31952step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31953Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31953step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31954Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31955Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw31955step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31955step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31956 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]
def raw31956Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31956step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw31956step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31956step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw31956step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -1, 3], ![-3, 3, 0]]
def raw31969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw31969step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31970 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]
def raw31970Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31970step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw31970step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31970step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw31970step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31974Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31974step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, -1, 3], ![-3, 3, 0]]
def raw31976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31976step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31976step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31977 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]
def raw31977Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31977step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![1, -1], ![2, -2]]
def raw31977step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31977step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![2, -2]]
def raw31977step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31977step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw31977step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31980Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw31982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw31982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw31983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw31984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31987step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw31988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw31988step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw31988step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw31997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31998step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw3200 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3200step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3200step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3200step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3201 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3201step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3202 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3202step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3202step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3202step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3202step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3202step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3203 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3203step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3203step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3204 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3204step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3204step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3204step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3204step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3204step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3205 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3205step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3205step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3206 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3206step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3206step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3207 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3207step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3207step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3207step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3207step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3207step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3208 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1]]
def raw3208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1]]
def raw3208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3208step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3208step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3209step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3209step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3209step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3209step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3209step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3209step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3210step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3210step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3210step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3210step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3210step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3211step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3211step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3211step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3211step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3212step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -2, 1], ![0, 2, -2]]
def raw3212step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3212step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw3212step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3212step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw3212step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3212step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw3212step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3213step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3213step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3213step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3214step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3214step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3215step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3215step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3216step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3216step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3216step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3216step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3216step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3216step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3217step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3217step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3217step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3217step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3218step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3218step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3218step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3219step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3219step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3220step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3220step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3220step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3220step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3220step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3220step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3220step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3220step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3221step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3221step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3221step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3222step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3222step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3223step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3224step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3224step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3224step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3224step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3224step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3224step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3225step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -3, 1], ![1, 1, -2]]
def raw3225step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3225step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw3225step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3225step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw3225step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3226step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3226step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3226step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3227step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3227step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3227step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3227step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3227step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3228step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3228step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3228step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3228step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3228step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, 2, -2]]
def raw3229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, 2, -2]]
def raw3229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3229step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![2, -3, 1], ![0, 2, -2]]
def raw3229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3229step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![2, -3, 1], ![0, 2, -2]]
def raw3229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3229step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw3229step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3229step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw3229step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw3230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw3230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw3230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3230step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw3230step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3230step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw3230step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3230step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw3230step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3231step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3232step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3233step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3233step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw3233step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3233step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3234step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3234step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3234step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3235step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3235step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3235step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3235step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3236step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3236step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3236step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3237step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3237step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3237step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3240step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3241step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3241step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3241step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3242step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3242step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3246step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3246step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3246step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3247step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3247step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3248step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3249step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3249step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3249step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3249step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3249step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3250step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3250step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3250step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3250step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3251step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3251step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3251step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3251step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3251step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3252step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3253step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3254step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3254step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]
def raw3255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]
def raw3255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]
def raw3255step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3255step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3256step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3256step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3256step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3256step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3256step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3256step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3257step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3257step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3257step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3258step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3261 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw3261step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3262 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw3262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3263 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw3263step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3263step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3263step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3264 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3264step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3264step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3264step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3264step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3264step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3265 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3265step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3265step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3265step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3265step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3265step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3266 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3266step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3266step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3266step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3266step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3267 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3267step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3267step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3267step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3268 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3268step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3268step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3268step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3268step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3269 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3269step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3269step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3270 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3270step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3270step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3271 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3271step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3271step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3271step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3271step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3271step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3272 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3272step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3272step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3272step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3273 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3273step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3273step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3273step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3273step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3274 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3274step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3274step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3275 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3275step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3275step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3276 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3276step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3276step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3276step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![0, -1, 1], ![0, -1, 1]]
def raw3276step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3276step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw3276step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw3276step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3276step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw3276step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3276step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3277 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3277step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3277step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3277step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3277step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3278 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3278step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, -1, 1], ![-1, 0, 1]]
def raw3278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3278step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3278step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3278step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3278step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3279 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3279step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3279step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw3279step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3279step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw3279step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3279step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw3279step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3280 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3280step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3280step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3281 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3281step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3281step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3281step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3282 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3282step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3282step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3282step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3282step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3282step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3283 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1]]
def raw3283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1]]
def raw3283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1]]
def raw3283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3283step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3283step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3283step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3284 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3284step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw3284step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3284step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw3284step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3284step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw3284step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3285 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3285step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3286 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3286step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3286step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3286step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3287 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3287step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3287step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3287step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3287step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3287step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3287step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3287step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3288 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3288step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3288step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3288step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3288step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3288step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3288step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0]]
def raw3289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3289step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw3289step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3289step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3289step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3289step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3289step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3290step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3290step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3290step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3290step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3291step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3291step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3291step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3291step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0]]
def raw3292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0]]
def raw3292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3292step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw3292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3292step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw3292step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3292step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3292step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3292step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3292step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0]]
def raw3293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1]]
def raw3293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3293step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3293step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]
def raw3293step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3293step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3293step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3293step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3293step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3293step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3293step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3294step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw3294step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3294step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3294step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical250
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw32000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw32007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw32011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32011step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw32012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32012step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw32016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32016step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw32016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32016step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw32016step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32017step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw32021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw32024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw32025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw32025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw32026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw32027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw32028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw32029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw32030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32034step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32035step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32035step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32036Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32036step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32037Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32038Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32038step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32038step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw32038step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32040step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32041step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32041step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32042Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32043step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32043step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32043step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32043step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw32043step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32044step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32044step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32045step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32045step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32046step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32046step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32047step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32047step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32048step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32048step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32049step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32049step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32050step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32050step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32050step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32051step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32051step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32052Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32052step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw32052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32053Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw32053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32054step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw32054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32054step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32055step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32061step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32062step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32063step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw32065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw32065step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32068step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32068step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32072step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32074step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32076Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32076step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw32077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32077step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32078Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32078step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw32078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32079step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32080Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32081Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32082Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32082step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32083Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32084step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32084step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32085Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32085step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32086step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32087step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw32088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32088step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32088step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw32089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32089step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32089step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32090step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32090step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32091step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32091step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32092step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw32093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw32093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32093step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32093step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32093step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32093step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw32094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw32094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32094step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32094step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32094step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32095Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32096Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw32097Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32097step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw32098Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32099Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32099step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32100Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32100step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32101Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw32102Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32102step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw32102step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32102step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32102step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw32103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw32103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw32124step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw32125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32126step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32126step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32127step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical251
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw32128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32128step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32129step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32130step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32130step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32130step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32131step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32131step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw32132step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw32132step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw32133step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw32133step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32134step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32134step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32135step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32135step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32136step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32137step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32138step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32138step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32138step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32139step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32139step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32140step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32140step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32141step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32141step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32142step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32142step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32143step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32144step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32145step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32145step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32146step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32146step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw32147step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw32147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw32148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw32148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw32148step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw32148step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32149step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32150step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32150step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32151step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw32152step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw32152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw32153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw32153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32153step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32154Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32154step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32154step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32154step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32154step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32155Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32155step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32155step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32155step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32156Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32156step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32156step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32157Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32157step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32157step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32157step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32158Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32158step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32158step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32159Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32159step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw32159step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32159step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32159step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32159step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32160Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw32160step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32160step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32160step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32160step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32160step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32161Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32161step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw32161step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32161step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32161step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32161step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32161step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32162Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32162step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw32162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw32162step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32162step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw32162step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32163Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32163step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw32163step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32163step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32163step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32163step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw32164step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32164step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32164step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32164step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32165Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw32165step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32165step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32165step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32165step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw32166step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32166step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32166step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32167Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw32167step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw32167step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32167step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw32167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32168step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32168step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32168step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32168step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32169Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32169step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw32169step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw32169step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32169step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw32169step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32170step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw32170step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw32170step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32170step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw32170step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32171Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw32171step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw32171step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32171step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw32171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32172step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw32172step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw32172step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32172step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw32172step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32173Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32173step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw32173step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32173step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32173step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32173step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32174step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw32174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw32174step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32174step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw32174step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32175step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw32175step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw32175step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw32176step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw32176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw32177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw32177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw32178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw32178step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32179step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw32179step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32179step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw32179step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32179step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw32179step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw32180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw32180step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32180step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw32180step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw32181step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw32181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32181step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw32181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32182step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw32182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw32182step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32182step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw32182step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw32183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw32183step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32186step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32187step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32189step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32191Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32192Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32193Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32194Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32194step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32195Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32196Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32196step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32196step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32197Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32197step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32197step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32198Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32198step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32199Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw32200Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw32200step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32200step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32201step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32202step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32202step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32203step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32203step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32204step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32204step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw32205step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32205step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32205step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32205step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32206step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32206step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32206step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32207step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32207step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32208step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32208step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32209step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32209step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw32210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw32210step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32210step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw32210step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32210step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32210step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32211Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32211step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32211step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32212Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32213Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32213step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32213step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32213step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32214Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32215Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32215step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32215step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32216Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32216step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32217Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32217step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32218Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32219Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32219step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32219step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw32219step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32219step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32219step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32220Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32220step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32221Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32222Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32222step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32223Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw32224Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32224step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw32224step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32224step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32224step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32225 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32225step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32225step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32225step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32226 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32226step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32226step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32227 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32227step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32227step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32227step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32228 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32228step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32228step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32228step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32229 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw32229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw32229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32229step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32230 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32230step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32230step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32230step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32231 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32231step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32231step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32232 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32232step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32232step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32233 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32233step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32233step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32233step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32234 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw32234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw32234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw32234step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw32234step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32235 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32235step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32235step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32236 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32236step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32237 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32237step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32237step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32237step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32238 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32238step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32239 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw32239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw32239step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32239step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw32239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32240 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32240step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32240step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32240step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32241 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32241step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32241step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32241step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32242 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32242step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32242step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32243 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32243step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32243step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32244 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw32244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw32244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw32244step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32244step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw32244step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32245 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32245step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32245step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32246 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32246step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32246step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32247 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32247step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32248 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32248step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32249 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw32249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw32249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw32249step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw32249step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32250 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32250step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32251 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32251step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32252 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32252step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32252step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32253 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32253step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32253step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32254 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32254step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32255Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical252
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw32256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32256Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32256step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32257Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw32258Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32258step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32259Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32260Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32260step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32261Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw32262Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32262step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw32263Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw32263step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32264Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32264step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32265Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32266Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw32268Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32268step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32270 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw32270Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32270step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw32270step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32270step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw32270step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32271Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32272step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32273Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw32274Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32274step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32276Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw32276step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32277Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32277step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32277step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32278Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32278step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![0, -1, 1], ![2, 0, -2]]
def raw32279Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32279step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1], ![1, 1, -2]]
def raw32280Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32280step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32281 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![-1, 1], ![2, -2]]
def raw32281Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32281step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw32281step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32281step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw32281step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw32291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32317 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32317step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32318 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32318step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32318step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32322 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32322step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32327 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32327step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32327step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32328 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32328step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32328step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32329 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw32329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32329step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32329step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32329step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32330 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32330step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32330step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32330step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32331 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32331step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32331step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32333 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32333step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32333step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32334 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32334step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32334step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32335 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32335step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32335step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32336 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32336step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32336step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32336step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32337 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32337step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32337step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32337step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw32382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32382step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32383step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical253
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw32384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32385step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32385step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32387step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32388step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32388step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32389step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw32390step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32390step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw32390step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw32391step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw32391step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32392step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32392step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32393step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32393step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32394step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32395step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32395step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32395step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32396step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32396step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32397step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32397step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32397step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32398step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32398step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32399step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32399step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32400step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32400step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32400step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32401step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32401step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32402step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32402step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32403step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32403step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32404step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32404step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32404step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32405step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32405step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32405step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32406step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32406step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32406step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32407step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32407step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32407step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32408step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32408step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32409step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32409step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32409step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32410step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32410step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw32411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw32411step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32411step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32411step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32411step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32415step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw32415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw32416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32418Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32419Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32420Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32420step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw32420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32421Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw32421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32422Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32423Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32424Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32425Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32425step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32425step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32426Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32427Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32428Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32429Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32430Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32430step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32431Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32432Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32433Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32434Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32435Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32436Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32437Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32438Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32439Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32440Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw32441Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw32441step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw32441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw32442step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw32442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32443step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32443step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32444step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32445step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32445step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32446step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw32447step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32447step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32447step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32447step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw32448step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw32448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32448step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw32448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw32449step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32449step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32449step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32449step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw32450step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw32450step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32450step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw32450step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32451Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw32451step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32451step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32451step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32451step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw32452step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32452step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32452step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32453Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw32453step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32453step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32453step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32453step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw32454step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32454step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32454step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32454step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32455Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32455step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw32455step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw32455step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32455step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw32455step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32456Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32456step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32456step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32456step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32456step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32457Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32457step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32457step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32457step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32457step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32458Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32458step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32458step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32458step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32458step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32459Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw32459step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw32459step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32459step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw32459step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32460Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32460step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw32460step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw32460step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32460step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw32460step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32461Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32461step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32461step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32461step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32461step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32462Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw32462step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32462step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32462step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32462step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32463Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw32463step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32463step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32463step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32463step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32464Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw32464step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32464step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw32464step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32464step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw32464step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32465Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw32465step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32465step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32465step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32465step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32466Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw32466step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32466step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32466step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32467Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw32467step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32467step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32467step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32467step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32467step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32468Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw32468step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32468step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32468step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32468step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32469Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw32469step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw32469step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32470Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw32470step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32470step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32470step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32470step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw32471Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw32471step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32471step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32471step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32471step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw32472step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw32476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw32476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32487 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32487step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32487step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32492 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32492step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32492step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32492step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw32493Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw32494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw32495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw32495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw32496Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw32502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32503 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]
def raw32503Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32503step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![3, -3]]
def raw32503step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32503step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw32503step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32503step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw32503step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32503step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw32503step3Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical254
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw32512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw32517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw32521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw32527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw32527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32528 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]
def raw32528Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32528step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]
def raw32528step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32528step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw32528step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32528step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw32528step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32529 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw32529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32530 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw32530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw32530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32531 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw32531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32532 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32532step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32533 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32534 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw32539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw32539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw32540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw32540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw32540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32541 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![2, -2], ![1, -1], ![0, 0]]
def raw32541Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32541step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![2, -2], ![1, -1]]
def raw32541step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32541step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw32541step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32541step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw32541step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32572step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32572step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32573step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32573step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32574step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32575step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32575step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw32576step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw32576step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32577step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32578step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32578step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32578step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32579step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32580step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32580step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32581step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32582step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32582step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32582step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32583step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32583step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32583step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32584step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw32585step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32585step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw32585step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32586step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32586step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32587step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32587step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32587step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32588step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32588step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32589step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw32590step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw32590step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw32591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw32591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32591step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32591step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32592step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32592step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32593step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32593step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32593step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32594step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32594step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32594step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw32595step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32595step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32595step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32595step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw32596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw32596step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw32596step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32596step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32596step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32596step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32597Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32597step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32597step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32597step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32597step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32597step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32597step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32598Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32598step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32598step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32598step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32599Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32599step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32599step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32599step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32599step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32599step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32600step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32600step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32600step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32600step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32600step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32600step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32601Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32601step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw32601step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32601step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32601step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32601step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32601step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32602Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32602step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw32602step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32602step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32602step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32602step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32603Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw32603step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32603step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32603step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32604Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32604step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw32604step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32604step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32604step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32604step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32605Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32605step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw32605step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32605step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32605step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32605step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32606Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32606step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw32606step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32606step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32606step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32606step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32607Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32607step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32607step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32607step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32608step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32608step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32609Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32609step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32609step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32609step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw32611step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32611step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw32611step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32611step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw32611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32612step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32612step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32612step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32612step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32612step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32613Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32613step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32613step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32613step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32613step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32613step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32614Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32614step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32614step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32614step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32615Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32615step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32615step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32615step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32615step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32615step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32615step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32616step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw32616step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32616step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32616step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32616step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32617Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32617step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32617step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32617step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32617step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32617step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32618step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32618step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32618step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32618step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32618step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32619Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32619step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32619step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32620step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32620step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32620step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32620step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw32621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw32621step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw32621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32621step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32621step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32621step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32622step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw32622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32622step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32622step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32623step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw32623step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw32623step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32623step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw32623step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw32624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32624step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32625step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw32625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32625step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32625step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32625step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw32626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw32626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw32626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32626step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32626step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32626step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical255
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw32669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw32670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32670step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32670step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw32671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw32672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32672step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw32672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32672step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32672step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32673step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32673step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32673step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32673step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32674step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32675step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32675step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32676step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw32677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw32677step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32677step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw32677step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw32678step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw32678step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32679step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32680step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32680step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32680step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32681step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32681step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32681step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32682step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32683step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32684step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32684step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32685step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32686step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32686step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw32687step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32687step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32687step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32687step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32688step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32688step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32689step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32690step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32690step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32691step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32691step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw32692step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw32692step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32693step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32693step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32693step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32694step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32694step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32695step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32695step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw32696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32696step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32696step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw32697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw32697step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw32698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw32698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw32698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw32698step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw32698step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32699Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32699step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32699step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32699step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32699step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32699step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32700Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32700step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32700step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32701Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32701step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32702step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw32702step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32702step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32702step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32702step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32702step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32703step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32703step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32703step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32703step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32704step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw32704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32704step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32704step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32704step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw32705step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32705step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32705step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw32706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32706step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32706step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw32707step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw32707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32707step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw32707step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32707step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw32707step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32708step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw32708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32708step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32708step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32708step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw32709step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32709step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1]]
def raw32710step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32710step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw32710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32710step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw32710step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw32711step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32711step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32711step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32711step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32711step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw32712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw32712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32712step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw32712step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw32713step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32713step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32714step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32714step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32714step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw32715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw32715step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32715step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw32715step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32716step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32716step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32717step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw32717step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32717step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw32717step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32717step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw32717step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32717step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw32717step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32718step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw32719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32719step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32719step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32719step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw32720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw32720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32720step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw32720step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw32721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32721step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw32722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32722step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32722step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32722step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw32723step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32723step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32723step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw32724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw32724step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32724step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw32724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw32725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw32725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw32726step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32726step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw32726step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw32727step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw32727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw32728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw32728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw32728step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw32728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw32728step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw32729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32730step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32731Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw32739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32739step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32744step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw32745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32745step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32746step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw32747step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32747step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32748step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32749step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32754step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32760step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw32761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw32761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw32761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw32762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw32763step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32763step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32764step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw32765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw32765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw32765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32765step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32766Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32766step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32766step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32767Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32767step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32767step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw32768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32768Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32768step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32768step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32768step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32769Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32769step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32769step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32770Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32770step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32770step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32770step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32770step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32770step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32771Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32771step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32771step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32771step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32771step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32771step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32771step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32771step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32771step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32772Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32772step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32772step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32772step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32773Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw32773step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32773step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32773step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32773step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32774Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32774step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32774step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32774step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32775Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32775step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32775step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32775step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32775step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32775step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32776Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32776step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw32776step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw32776step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32776step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw32776step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32777Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw32777step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32777step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32777step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32777step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32777step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32778Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32778step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw32778step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32778step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32778step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32778step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32778step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32779Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32779step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw32779step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32779step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32779step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32779step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32780Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32780step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw32780step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw32780step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32781Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw32781step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw32781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32782Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32782step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32782step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32782step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw32783Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw32783step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw32783step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw32783step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32784Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32784step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw32784step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw32784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32785Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32785step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32785step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32786Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32786step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32786step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw32787Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw32787step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw32787step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw32787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32788Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32790step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw32791step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32791step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32791step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32791step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw32792step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32792step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32792step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32792step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32793step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw32793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32793step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw32794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32795step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32796step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32796step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32798step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32799step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32799step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32800step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32800step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32801step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32802step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw32802step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw32802step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32803step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32803step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32822 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32822step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32822step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32822step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32822step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32824 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32824step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32824step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32826 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw32826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw32826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32826step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32826step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32826step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32827 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32827step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32827step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32830 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32830step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32830step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32830step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32834 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw32834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw32834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32834step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32834step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32835 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32835step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32835step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32835step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32850step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32853step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw32855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32855step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32856Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32856step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32856step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32856step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32857Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32857step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32857step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32857step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32857step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32858Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32858step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32858step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32858step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32859Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32859step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32859step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32859step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32859step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32860Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw32860step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32860step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32860step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32861Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32861step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32861step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32861step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32861step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32861step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32862Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32862step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32862step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32862step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32863Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32863step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32863step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32863step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32863step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32864Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32864step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32864step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32864step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32864step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32865Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw32865step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32865step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32865step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32866Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32866step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32866step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32866step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32867Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32867step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32867step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32867step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32867step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32868Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw32868step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw32868step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32868step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw32868step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32869Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32869step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32869step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32869step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32869step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32870Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32870step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32870step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32870step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32871Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32871step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32871step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32871step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32872Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw32872step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw32872step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32872step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw32872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw32873Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32873step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32873step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32873step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32873step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32873step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32874Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw32874step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw32874step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32874step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw32874step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32875Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw32875step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw32875step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32875step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw32875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32876Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32876step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32876step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw32877Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32877step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32877step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32881step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32881step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32881step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32882step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32882step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32883step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32883step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw32884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32884step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32885step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32886step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32887step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, -1, -1]]
def raw32888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32888step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32889step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32890step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32891step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32892step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw32893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw32893step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32893step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw32893step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw32894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw32894step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw32894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw32895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw32895step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw32895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

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

def raw32896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw32896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw32896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw32896step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32896step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32896step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32896step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -2, -1]]
def raw32897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw32897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw32897step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32897step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32897step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32897step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32902 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32902step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32902step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32902step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32902step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32905step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32906 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw32906step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32906step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32906step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32906step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32909 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32909step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32909step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32918step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw32921step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32921step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32921step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32922step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32922step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32922step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32922step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32922step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32923step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw32936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw32937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw32939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw32939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw32939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32939step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32940step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32940step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32941step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32941step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32942step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32942step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32942step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32944step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32944step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32945step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32945step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32945step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32945step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32945step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32946step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32946step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw32947step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32947step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32947step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32947step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32948step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32948step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32948step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32948step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32949step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32949step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32949step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw32950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw32950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32950step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw32950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw32951step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32951step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw32951step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32951step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw32951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32952step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw32952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32952step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32952step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32952step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw32953step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32953step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32953step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw32954step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw32954step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32954step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw32954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end


