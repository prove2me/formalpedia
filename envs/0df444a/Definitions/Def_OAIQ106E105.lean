-- Prove2me | Definitions.Def_OAIQ106E105
-- name    : OAIQ106E105
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:15:21.60332+00:00
-- url     : https://prove2.me/theorems/0a49fc0b-75ac-428c-9ebe-fb15358fa75d
-- title:
--   Definitions bundle OAIQ106E105 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7474 declarations of OpenAI's Lean: 7474 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw3028step1`, `OAI.MUB6.Certificate.MixedSemantics.raw3028step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw3028step2`, `OAI.MUB6.Certificate.MixedSemantics.raw3028step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw3028step3`, `OAI.MUB6.Certificate.MixedSemantics.raw3028step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw3029`, `OAI.MUB6.Certificate.MixedSemantics.raw30290`, `OAI.MUB6.Certificate.MixedSemantics.raw30290Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw30290step0`, `OAI.MUB6.Certificate.MixedSemantics.raw30290step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw30290step1`, `OAI.MUB6.Certificate.MixedSemantics.raw30290step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw30290step2`, `OAI.MUB6.Certificate.MixedSemantics.raw30290step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw30290step3`, `OAI.MUB6.Certificate.MixedSemantics.raw30290step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw30291`, `OAI.MUB6.Certificate.MixedSemantics.raw30291Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw30291step0`, `OAI.MUB6.Certificate.MixedSemantics.raw30291step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw30291step1`, `OAI.MUB6.Certificate.MixedSemantics.raw30291step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw30291step2`, `OAI.MUB6.Certificate.MixedSemantics.raw30291step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw30291step3`, `OAI.MUB6.Certificate.MixedSemantics.raw30291step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw30292`, `OAI.MUB6.Certificate.MixedSemantics.raw30292Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw30292step0`, `OAI.MUB6.Certificate.MixedSemantics.raw30292step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw30292step1`, `OAI.MUB6.Certificate.MixedSemantics.raw30292step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw30292step2`, `OAI.MUB6.Certificate.MixedSemantics.raw30292step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw30293`, `OAI.MUB6.Certificate.MixedSemantics.raw30293Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw30293step0`, `OAI.MUB6.Certificate.MixedSemantics.raw30293step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw30293step1` and 7434 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Certificate_MixedTargetBasic`, `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical23`, `MutuallyUnbiased_MixedSemantics_Canonical236`, `MutuallyUnbiased_MixedSemantics_Canonical237`, `MutuallyUnbiased_MixedSemantics_Canonical238`, `MutuallyUnbiased_MixedSemantics_Canonical239`, `MutuallyUnbiased_MixedSemantics_Canonical24`, `MutuallyUnbiased_MixedSemantics_Canonical240`, `MutuallyUnbiased_MixedSemantics_Canonical241`, `MutuallyUnbiased_MixedSemantics_Canonical242`, `MutuallyUnbiased_MixedSemantics_Canonical243`, `MutuallyUnbiased_MixedSemantics_Canonical244`, `MutuallyUnbiased_MixedSemantics_Canonical245`, `MutuallyUnbiased_MixedSemantics_Canonical246`, `MutuallyUnbiased_MixedSemantics_Canonical247`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E130`, `OAIQ106E134`, `OAIQ106E135` and `OAIQ106E137`; the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound2936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2939_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2941_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2943_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2957_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1826_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_MixedTargetBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

abbrev OriginalKey := Fin 5502 ⊕ Fin 8

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]

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

def raw302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw302step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw302step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw302step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw303 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw303Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw303step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw304 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw304step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw304step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw305 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw305Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw305step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw306 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw306step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw307 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw307Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw307step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw307step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw308 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw308step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw309 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw309Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw309step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw309step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw310 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw310step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw311 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw311Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw311step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw314 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw314step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw315 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw315Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw315step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw316 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw3028step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3028step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3028step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3028step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3029step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3029step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3029step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3029step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3029step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3030step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3030step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3030step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3031step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3031step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2]]
def raw3032step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3032step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![1, 1, -2]]
def raw3032step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3032step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3032step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3032step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3032step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2]]
def raw3033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3033step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3033step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3033step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3033step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3033step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3033step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3034step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3034step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3034step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3034step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3035step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3035step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3035step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3035step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3036step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3036step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw3037step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3037step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw3037step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw3038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3038step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3038step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3038step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3038step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3039step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3039step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3039step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3041step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3041step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3042step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3042step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3043step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3043step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3043step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3043step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3044step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3044step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3044step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3046step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3046step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3047step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3048step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3048step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3048step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3048step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw3049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3049step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw3049step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3049step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw3049step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3050step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3050step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2]]
def raw3050step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3050step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3050step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3050step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3050step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3050step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3050step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3051step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3051step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3052step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3052step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3052step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2]]
def raw3053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2]]
def raw3053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![0, 2, -2]]
def raw3053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw3053step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3053step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw3053step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3054step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw3054step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3054step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3054step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3054step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3054step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3055step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw3055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3055step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw3055step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3055step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw3055step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3056step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3056step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3056step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3056step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3057step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3057step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3057step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw3058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw3058step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw3058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3058step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw3058step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3058step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw3058step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3058step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw3058step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3059step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3059step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3059step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3059step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3060step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3061step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3062step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3062step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2]]
def raw3062step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3062step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![1, 1, -2]]
def raw3062step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3062step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3062step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3063step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2]]
def raw3063step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3064step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3064step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3065step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3066step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3067step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw3067step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3067step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw3067step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3067step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw3067step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3068step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw3068step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw3068step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3069step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3069step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3070step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3070step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical236
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30290step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw30290step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30290step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30290step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30290step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30291step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw30291step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30291step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30291step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30291step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw30292step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30292step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30292step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30292step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw30293Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw30293step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw30293step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw30293step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw30293step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30294step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw30294step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw30294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30295step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30295step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30296step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30296step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30297step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30297step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw30298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30298step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw30298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw30298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30299Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30299step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30299step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30300Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30300step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30301Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30301step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30302Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30302step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30302step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30303Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30303step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30303step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30304Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30304step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30305 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]
def raw30305Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30305step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]
def raw30305step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30305step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw30305step1Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical237
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30363 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30363step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30363step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30365 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw30365step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30365step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30365step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30365step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30370 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30370step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30370step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30375 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30375step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30375step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30375step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30380 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30380step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30380step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30380step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30381 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30381step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30381step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30381step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30387 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30388 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw30388step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30388step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30412step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30413step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30414step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30415step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw30416step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30418step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw30421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30421step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30422step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw30426step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw30432step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw30433step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30433step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw30434step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw30434step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw30434step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30434step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw30434step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30435step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30435step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30435step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30435step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw30436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw30436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30436step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw30439step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw30439step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30439step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw30439step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30440step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30440step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30440step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30440step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30442step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30442step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30442step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30442step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30442step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30443step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw30443step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw30443step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30443step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw30443step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30444step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30444step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30444step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30445step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw30445step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30445step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30445step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30445step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw30446step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw30446step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30446step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30446step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30446step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30447step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30447step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30447step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30447step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30447step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30448step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw30448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw30448step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30448step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw30448step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30449step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30449step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30449step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30449step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw30450step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30450step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30450step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30450step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30451Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw30451step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw30451step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30451step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30451step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30451step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30452step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw30452step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30452step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw30452step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30452step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw30452step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30453Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30453step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw30453step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw30453step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30453step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw30453step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw30454step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30454step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw30454step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30454step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw30454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30455Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30455step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw30455step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw30455step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30455step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw30455step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30456Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw30456step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw30456step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw30456step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30456step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw30456step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30457Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30457step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30457step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30457step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30457step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30458Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30458step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30458step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30458step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30458step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30459Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw30459step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw30459step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30459step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw30459step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30460Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw30460step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30460step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30460step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30461Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw30461step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30461step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30461step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30461step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30462Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw30462step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw30462step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30462step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30462step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30462step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30463Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw30463step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30463step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30463step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30463step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical238
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30464Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw30464step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30464step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30464step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30464step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30465Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30465step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30465step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw30466Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw30466step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw30466step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30466step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30466step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30466step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30466step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30467Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30467step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw30467step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30467step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30467step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30467step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30467step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30468Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30468step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30468step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30468step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30469Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30469step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30469step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30469step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30469step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30470Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30470step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30471Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30471step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw30471step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30471step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30471step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30471step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30471step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30472step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw30476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30541 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30541step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30541step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30545 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30545step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30545step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30547 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30547step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30547step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30547step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30548 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30548step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30548step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30548step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30548step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30555 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30555Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30555step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30556 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30556Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30556step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw30556step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30556step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw30601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30601step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30601step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30601step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30602step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30603step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30603step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![2, 1, -3], ![1, -1, 0]]
def raw30604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30604step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30604step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30604step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw30605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw30605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw30605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw30606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw30607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw30608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw30609step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw30610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw30611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw30612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw30613step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, 0, -3], ![2, -2, 0]]
def raw30614step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30614step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw30614step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![3, 0, -3], ![2, -2, 0]]
def raw30615step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30615step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw30615step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30615step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw30615step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30616step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30616step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30617step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw30618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw30618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![3, 0, -3], ![1, -1, 0]]
def raw30618step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30618step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30618step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30618step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw30619step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def raw30620step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw30620step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30620step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30620step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30620step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30620step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30621step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30621step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30621step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30621step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30622step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30622step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30622step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30623step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw30623step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30623step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30623step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30623step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30623step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30624step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30625step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![2, 1, -3], ![1, -1, 0]]
def raw30626step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30626step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30626step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30626step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30626step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw30627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw30627step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw30627step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw30627step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30627step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw30627step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30628step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw30628step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30628step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw30628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30629step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw30629step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30629step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw30629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30631step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30631step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30631step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30632step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw30632step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30632step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw30632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30633step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw30633step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw30633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30635step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30635step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30636step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, 0, -3], ![2, -2, 0]]
def raw30636step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw30636step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30636step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw30636step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30637Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30637step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![3, 0, -3], ![2, -2, 0]]
def raw30637step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw30637step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30637step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw30637step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30638Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30638step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30638step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30639Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30639step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30639step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw30640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw30640step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![3, 0, -3], ![1, -1, 0]]
def raw30640step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30640step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30640step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30640step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30641Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30641step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw30641step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw30641step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30641step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw30641step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30642Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30642step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def raw30642step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw30642step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30642step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw30642step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30643Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30643step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw30643step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw30643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30644Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30644step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw30644step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30644step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw30644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30699 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -3, 2], ![-1, -1, 2]]
def raw30699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw30699step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30699step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw30699step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30699step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw30699step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30702step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30702step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30702step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30703step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30703step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30704step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw30705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30706step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30706step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw30706step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw30706step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw30706step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw30706step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw30706step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30707step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30710step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30711step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30712step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30716step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30717step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

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

def raw3072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3072step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3072step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3072step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw3072step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3073step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw3073step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3074step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3075Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3075step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3076Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3077step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3077step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3077step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3077step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw3077step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3078Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3078step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw3078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3079step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw3079step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3079step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw3079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3080Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3080step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3080step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2]]
def raw3080step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3080step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3080step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3080step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3081Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3081step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3081step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3081step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3082Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3082step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2]]
def raw3083Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2]]
def raw3083step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![0, 2, -2]]
def raw3083step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3083step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw3083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3083step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw3083step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3084step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw3084step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3084step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3085Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3085step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw3085step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3085step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3086Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3086step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3087Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3087step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw3088Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw3088step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw3088step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3088step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw3088step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3088step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw3088step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1]]
def raw3089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3089step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3089step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3089step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3089step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3090step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3090step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3091step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3091step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1]]
def raw3092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1]]
def raw3092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw3092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3092step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3092step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3092step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3092step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1]]
def raw3093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1]]
def raw3093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw3093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3093step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3093step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3093step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3093step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw3094step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3094step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3094step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3094step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3095step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3095step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3096step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3096step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1]]
def raw3097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1]]
def raw3097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw3097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3097step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3097step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3097step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3097step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1]]
def raw3098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1]]
def raw3098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw3098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3098step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3098step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3099step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3099step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3100step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3100step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3100step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3100step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3101step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3101step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3101step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1]]
def raw3102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1]]
def raw3102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3102step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3102step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1]]
def raw3103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1]]
def raw3103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3103step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3104step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3104step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3105step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3105step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3105step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3105step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3106step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3106step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3106step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1]]
def raw3107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1]]
def raw3107step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3107step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3107step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1]]
def raw3108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1]]
def raw3108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3108step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1]]
def raw3109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1]]
def raw3109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw3109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3109step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3109step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3109step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1]]
def raw3110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1]]
def raw3110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![2, -1, -1], ![1, -2, 1]]
def raw3110step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3110step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw3110step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3110step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw3110step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1]]
def raw3111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1]]
def raw3111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3111step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3111step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3111step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3111step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1]]
def raw3112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1]]
def raw3112step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3112step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3112step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3112step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3112step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1]]
def raw3113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1]]
def raw3113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![0, -1, 1]]
def raw3113step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3113step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3113step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw3114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw3114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw3114step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3114step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw3114step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3114step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw3114step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw3115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw3115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw3115step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3115step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3115step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3115step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3115step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw3116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw3116step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3116step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3116step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw3117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw3117step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3117step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3117step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1]]
def raw3118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1]]
def raw3118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw3118step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3118step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3118step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3118step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3118step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3119step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3121step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3121step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3121step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3121step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw3122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3122step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3122step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3122step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3122step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3122step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3123step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3123step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3123step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3123step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3124step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3125step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3126step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3126step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3126step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3126step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw3127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3127step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3127step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3127step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3127step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3127step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3128step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3128step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3129step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3129step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3129step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3131step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3131step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw3132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3132step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3133step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3133step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3134step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3134step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3136step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3137step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3138step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw3139step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw3139step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3140step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3140step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3140step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3140step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3141step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3141step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3141step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3141step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw3142step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3142step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3142step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3142step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1]]
def raw3143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1]]
def raw3143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3143step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3144step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3146step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3146step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3147step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw3148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw3148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3148step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3149Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3149step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw3149step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3149step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3150Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3150step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3151Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3151step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3151step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3152Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw3152step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3152step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3152step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3153Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3153step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3154Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3154step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3154step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3155Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3155step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw3157step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3157step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3157step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3158step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3159step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3160step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw3162step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30721step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30721step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw30721step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30722step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30722step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw30722step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30723step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw30725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw30725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw30725step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30728step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30728step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30728step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30728step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30728step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30729step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30729step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30729step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30730step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30730step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30730step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30732step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw30733step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw30733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30733step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw30733step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30733step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw30733step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30734step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30734step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30734step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw30734step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30734step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw30734step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30735step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30735step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30735step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30735step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30735step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30735step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30736step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30736step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30736step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30736step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30736step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30737step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30737step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30737step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30738step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30738step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30738step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30738step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30738step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30738step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30738step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30738step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30739step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30739step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30739step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30739step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30739step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30740step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30740step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30740step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30741step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30741step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw30742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw30742step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30742step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw30742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30743step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30743step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30743step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30743step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30744step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30744step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30744step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30744step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30744step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30745step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30745step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30745step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30746step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30746step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw30747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw30747step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30747step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw30747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30748step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30748step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30748step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30749step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30749step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw30749step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30749step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw30749step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30749step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw30749step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30750step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30750step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30750step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw30750step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30750step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw30750step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30751step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30752step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw30753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw30753step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30753step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30753step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30753step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30753step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30754Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30754step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30754step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30754step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw30754step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30754step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30754step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30754step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30754step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30755Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30755step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30755step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30755step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30755step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw30755step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30755step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw30755step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30755step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw30755step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30756step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw30756step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30756step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30756step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30756step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30757step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw30757step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30757step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30757step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30757step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw30765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30765step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30767step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw30767step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw30767step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw30767step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw30767step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw30767step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw30767step4 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw30767step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30768step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30768step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30769step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30784step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30786step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw30786step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30786step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30788step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30788step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw30789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw30789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30789step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30789step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30790step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw30791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30791step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30793step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw30794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw30794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30794step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30794step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30833 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30833step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30833step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30833step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30833step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30836 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30836step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2]]
def raw30836step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30836step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw30836step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw30836step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw30836step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw30836step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw30836step4Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical241
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30868 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2], ![0, 0]]
def raw30868Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30868step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw30868step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, 0, -2], ![2, -1, -1]]
def raw30869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![2, -1, -1]]
def raw30870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, -1, -1]]
def raw30871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30871step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw30873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1]]
def raw30874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30875 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![0, 0], ![2, -2], ![1, -1]]
def raw30875Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30875step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![2, -2], ![1, -1]]
def raw30875step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30875step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw30875step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30888step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw30888step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw30888step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw30888step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30889step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30890step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30890step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30890step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30891step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30891step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30891step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 1, -2]]
def raw30892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 1, -2]]
def raw30892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![2, 0, -2], ![1, 1, -2]]
def raw30892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30892step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30892step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30892step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30893step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30896step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 1, -2]]
def raw30897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2], ![1, 1, -2]]
def raw30897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw30897step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30897step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 1, -2]]
def raw30902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![1, 1, -2]]
def raw30902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 1, -2]]
def raw30907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![1, 1, -2]]
def raw30907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30907step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw30908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30908step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw30908step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 0, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30909step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![3, -1, -2], ![2, 0, -2]]
def raw30909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30909step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 0, -2], ![3, -1, -2]]
def raw30909step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30910step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw30910step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30910step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30911step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw30911step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30911step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 1, -2]]
def raw30912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2], ![1, 1, -2]]
def raw30912step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![3, -1, -2], ![1, 1, -2]]
def raw30912step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw30912step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30913step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw30913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 0, -2], ![3, -1, -2]]
def raw30914step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30915step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw30915step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30915step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30916step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw30916step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30916step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30917step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw30917step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30922 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30922step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30922step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30922step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30922step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30922step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw30936step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30936step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw30936step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30936step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw30936step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30937step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30937step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30937step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30937step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30938step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30938step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30938step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30938step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw30939step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30939step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw30939step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30939step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw30939step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30940step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw30940step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30940step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30940step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30940step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30940step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30941step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30941step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30945step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30946step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30949step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30950step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30950step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30950step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30951step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30952step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw30953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw30953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![3, -1, -2], ![1, -1, 0]]
def raw30953step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30953step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30953step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30954step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30954step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, -1, 3], ![-3, 3, 0]]
def raw30954step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30954step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30954step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30954step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30954step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30955step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw30955step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30955step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30955step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30955step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw30956step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30956step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30956step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30956step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw30957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw30957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30957step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30958step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30958step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -2, 3], ![-2, 2, 0]]
def raw30958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30958step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw30958step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw30959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30959step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw30960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30961step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw30961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30961step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw30961step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30962step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw30962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30962step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw30962step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30963step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw30967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30968step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw30971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30972step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-2, -1, 3], ![-3, 3, 0]]
def raw30972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 1, -3], ![3, -3, 0]]
def raw30972step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30973step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw30973step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30973step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30974step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw30974step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw30975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw30975step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![3, -1, -2], ![1, -1, 0]]
def raw30975step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30975step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, -1, 2], ![-3, 3, 0]]
def raw30975step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30975step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw30975step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical242
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30976step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30976step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, -1, 3], ![-3, 3, 0]]
def raw30976step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30976step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30977step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw30977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30978step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw30978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw30979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw30979step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30979step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw30979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30979step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30979step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30980step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30980step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw30980step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30980step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw30980step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30980step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw30980step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30981step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30981step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30981step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30981step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30981step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30982step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30982step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30982step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30982step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30983Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30983step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30983step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw30983step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30983step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw30983step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30983step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw30983step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30984Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30984step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30984step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30984step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30984step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw30984step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30984step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30984step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30984step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30984step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30985step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30985step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30985step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30985step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30985step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30985step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30985step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30985step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30986step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw30986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw30986step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30986step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw30986step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30987step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30987step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30988step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw30988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw30988step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30988step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw30988step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30989step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw30989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30989step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30989step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30989step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw30990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw30990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30990step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw30990step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30991step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30991step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30991step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30992step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw30992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw30992step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30992step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw30992step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30993step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw30993step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30993step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30993step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30993step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30993step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30994step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30994step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-2, -1, 3]]
def raw30994step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30994step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw30994step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30994step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw30994step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw30995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30995step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30995step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw30996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30996step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30996step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30996step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw30997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw30997step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![3, -1, -2], ![1, -1, 0]]
def raw30997step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw30997step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30997step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw30997step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30997step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw30997step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30998step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def raw30998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def raw30998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw30999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw30999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw31000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw31000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw31001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw31001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31001step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw31001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31001step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw31001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -2, 3], ![-2, 2, 0]]
def raw31002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw31002step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31005step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw31005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31009step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -2, 0], ![2, 0, -2]]
def raw31009step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31009step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31009step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31010step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31010step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31010step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31010step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31010step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31011step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31011step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31011step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31011step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31011step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw31012step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw31012step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31012step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw31012step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31013step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31013step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31014step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31014step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31014step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31015step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31015step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31015step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31016step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31016step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31017step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31017step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31018step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31018step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31019step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31019step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![3, -3, 0], ![2, 0, -2]]
def raw31020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31020step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw31020step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31020step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw31020step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![3, -3, 0], ![2, 0, -2]]
def raw31021step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31021step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw31021step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31021step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw31021step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw31022step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw31022step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31022step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw31022step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw31023step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw31023step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31023step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw31023step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw31024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw31024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31024step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![3, -3, 0], ![1, 1, -2]]
def raw31024step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31024step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw31024step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31024step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw31024step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31025step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -2, 0], ![3, -1, -2]]
def raw31025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31025step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31025step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31025step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31025step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -2, 0], ![3, -1, -2]]
def raw31026step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31026step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31026step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31026step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31026step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31027step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31027step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31028step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31028step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31029Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31029step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -2, 0], ![2, 0, -2]]
def raw31029step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31029step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31029step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31030Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31030step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31030step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31031Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31031step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31032Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31032step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw31032step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31032step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31033Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31033step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -2, 0], ![1, 1, -2]]
def raw31033step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31033step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31033step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31034Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31034step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw31034step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31035Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31035step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31036Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31036step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31037Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31037step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw31037step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31037step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw31037step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31038Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31038step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw31038step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31038step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31039step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31040step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31042Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31042step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31043step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31044Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31044step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31044step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31045Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31045step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31045step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31046Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31047Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31047step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31048Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31048step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31049Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31049step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![3, -3, 0], ![2, 0, -2]]
def raw31049step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31049step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw31049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31050Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31050step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31050step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![3, -3, 0], ![2, 0, -2]]
def raw31050step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31050step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw31050step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31051Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31051step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw31051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw31051step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31052Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31052step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw31052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw31052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw31053Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw31053step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![3, -3, 0], ![1, 1, -2]]
def raw31053step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw31053step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31054step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31054step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -2, 0], ![3, -1, -2]]
def raw31054step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31054step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31054step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31055step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -2, 0], ![3, -1, -2]]
def raw31055step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31055step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31055step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31056step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31057step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw31058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw31058step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw31058step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31058step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31058step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31064 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw31064step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31064step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw31064step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31068 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31068step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31068step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31068step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31068step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31068step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31073 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31073step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31073step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31073step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw31079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31079step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31079step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31079step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31079step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31079step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31079step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31080 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31080step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31080step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31080step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31080step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31081 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31081Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31081step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31082 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31082Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31082step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31083 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31083Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31083step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31083step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31083step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31084 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31084step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw31084step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31084step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31085Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31085step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw31085step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31085step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31086 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31086Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31086step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31087 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31087Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31087step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31088 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31088Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31088step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31088step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw31088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31089 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31089Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31089step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw31089step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31089step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -3, 1], ![2, 0, -2]]
def raw31089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31090Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31090step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31091 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31091Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31091step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31092 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31092Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31092step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31093 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31093Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31093step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31093step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31094Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31094step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31095 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31095Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31095step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31095step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31096 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31096Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31097 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31097Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31097step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31098 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31098Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31098step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31099Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31099step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31099step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -3, 2], ![-2, 0, 2]]
def raw31099step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31099step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31099step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31100 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31100Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31100step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -3, 2], ![-2, 0, 2]]
def raw31100step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31101 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31101Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31101step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw31101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31102 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31102Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31102step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw31102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31103 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw31103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw31103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -3, 2], ![-3, 1, 2]]
def raw31103step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31103step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -3, 1], ![2, 1, -3]]
def raw31103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical243
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw31104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31104step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw31104step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31105 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31105step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw31105step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31106 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31106step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31107 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31107step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31108 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31108step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31108step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31108step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31108step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31109 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31109Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31109step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw31109step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31109step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31109step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31109step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31110 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31110step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31110step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31110step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31111 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31111Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31111step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31111step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31111step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31112 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31112step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31112step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31112step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw31112step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31112step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw31112step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31113Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31113step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw31113step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31113step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw31113step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31113step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw31113step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31114step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw31114step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31114step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-2, 2, 0], ![-2, -1, 3]]
def raw31114step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31114step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -2, 0], ![2, 1, -3]]
def raw31114step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31114step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -2, 0], ![2, 1, -3]]
def raw31114step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31115 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31115Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31115step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31115step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31116 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31116Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31116step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31116step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31117 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31117Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31117step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31117step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw31117step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31117step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw31117step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31118 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31118Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31118step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw31118step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31118step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-2, 2, 0], ![-2, -1, 3]]
def raw31118step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31118step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -2, 0], ![2, 1, -3]]
def raw31118step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31118step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -2, 0], ![2, 1, -3]]
def raw31118step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31119Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31119step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31119step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31119step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31119step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31119step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31120 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31120Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31120step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31120step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31121 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31121Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31121step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31121step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31122 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31122Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31122step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31122step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31122step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31123 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31123Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31123step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31123step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31123step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31123step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31123step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31124Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31124step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31124step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31124step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31124step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31124step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31125 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31125Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31125step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31125step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31125step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31125step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31126 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31126Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31126step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31126step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31127 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31127Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31127step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31127step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31128 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31128Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31128step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31128step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31128step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31128step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31128step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31129Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31129step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -3, 2], ![-2, 0, 2]]
def raw31129step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31129step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, -1, 2], ![-3, 2, 1]]
def raw31129step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31129step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw31129step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31129step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw31129step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31130 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31130Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31130step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31130step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -3, 2], ![-2, 0, 2]]
def raw31130step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31130step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw31130step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31130step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw31130step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31131 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31131Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31131step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw31131step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw31131step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31132 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31132Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31132step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw31132step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw31132step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31133 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw31133Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw31133step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -3, 2], ![-3, 1, 2]]
def raw31133step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31133step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 2, -3], ![3, -3, 0]]
def raw31133step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31133step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 2, -3], ![3, -3, 0]]
def raw31133step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31134Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31134step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw31134step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31134step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31134step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31134step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw31134step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31134step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw31134step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31135 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31135Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31135step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31135step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw31135step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31135step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -2, 0], ![2, -1, -1]]
def raw31135step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31135step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -2, 0], ![2, -1, -1]]
def raw31135step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31136 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31136Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31136step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31136step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31136step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31137 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31137Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31137step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31137step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31137step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31137step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31138 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31138Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31138step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31138step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31138step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31138step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw31138step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31138step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw31138step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31139step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw31139step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw31139step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw31139step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw31139step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw31139step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31140step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31140step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31140step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31140step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31141step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31141step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31141step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31141step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31141step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31142step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31142step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31142step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw31142step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31142step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw31142step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31142step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw31142step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31145step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31148step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31149step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31150step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![3, -2, -1], ![1, 0, -1]]
def raw31152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31153step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31153step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31155step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31156step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31156step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -2, 3]]
def raw31156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31156step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw31156step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31157step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw31157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31157step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw31157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31158step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw31158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw31158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31159step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31159step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31159step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31159step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw31159step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31159step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw31159step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31160step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31160step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31160step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31160step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw31160step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31160step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw31160step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31161step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31163step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31164step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31169step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31169step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, -1, 3], ![-3, 3, 0]]
def raw31169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31169step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def raw31169step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![3, -2, -1], ![1, 0, -1]]
def raw31172step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, -1, 2], ![-3, 3, 0]]
def raw31172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31172step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw31172step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31173step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, -1, 3], ![-3, 3, 0]]
def raw31173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31173step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def raw31173step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31175step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31176step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31176step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw31176step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31176step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw31176step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31176step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw31176step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31177step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31177step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31177step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31178step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31178step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31178step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31178step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31179step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31179step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31179step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31179step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw31179step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31179step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw31179step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31179step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw31179step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw31180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw31180step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31180step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw31180step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31181step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31181step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31182step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw31182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw31182step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31182step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw31182step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31183step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw31183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw31183step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31183step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw31183step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31184step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31184step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31184step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31185step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw31185step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw31185step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31185step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw31185step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31186step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31186step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 3, -2], ![-1, -1, 2], ![-1, -2, 3]]
def raw31186step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31186step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw31186step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31186step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw31186step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31187step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw31187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31187step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31187step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31187step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31187step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw31188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31188step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31188step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31188step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31189step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![3, -2, -1], ![1, 0, -1]]
def raw31189step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31189step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw31189step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31189step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw31189step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31189step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw31189step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31190step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31190step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31190step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 3, -2], ![-1, -1, 2], ![-1, -2, 3]]
def raw31190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31190step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw31190step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31190step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw31190step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31191step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw31191step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31191step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31191step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31191step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31192step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw31192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31192step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31192step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31192step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31193step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31193step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -2, 3]]
def raw31193step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31193step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw31193step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31196step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31196step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31196step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31197step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31197step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31197step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31198step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31199step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31200step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31200step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31201step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31201step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31202step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31202step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31203step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31203step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31204step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31204step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31204step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31205step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31205step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31206step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31206step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31207step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31207step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31207step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31208step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![3, -2, -1], ![2, -1, -1]]
def raw31208step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31208step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31208step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31208step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31208step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31209step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![3, -2, -1], ![2, -1, -1]]
def raw31209step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31209step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31209step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31209step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31209step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31210step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31210step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31211step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31211step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![3, -2, -1], ![1, 0, -1]]
def raw31212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31212step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31212step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31212step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31212step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -1, -1], ![3, -2, -1]]
def raw31213step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31213step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31213step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![3, -2, -1]]
def raw31214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31214step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31214step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31214step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31214step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31215step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31215step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31216step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31216step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31217Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31217step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31218Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31218step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31219Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31220Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31220step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31221Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31221step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31221step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31222Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31222step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31223Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31224Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31224step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31224step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31225Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31225step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![3, -2, -1], ![2, -1, -1]]
def raw31225step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31225step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31226Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31226step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![3, -2, -1], ![2, -1, -1]]
def raw31226step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31226step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31227Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31227step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31227step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31228Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31228step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31228step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31229Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31229step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31229step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![3, -2, -1], ![1, 0, -1]]
def raw31229step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31229step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31229step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31230Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31230step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -1, -1], ![3, -2, -1]]
def raw31230step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31230step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31230step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31231Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31231step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![3, -2, -1]]
def raw31231step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31231step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31231step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical244
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw31232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31232Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31232step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31233Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31233step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31233step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-1, -1, 2], ![-2, 3, -1]]
def raw31234step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31234step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw31234step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31234step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw31234step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31235 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![-2, 3, -1]]
def raw31235step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw31235step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31235step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw31235step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31236 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![-2, 3, -1]]
def raw31236step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31236step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw31236step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31236step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw31236step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31237step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31237step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31237step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31237step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31238 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31238step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31238step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31238step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31238step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31239step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31239step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31239step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31239step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31239step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31240 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31240step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31240step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31240step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31240step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31240step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31241 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw31241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31241step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31241step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31241step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31241step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw31242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31242step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31242step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31242step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31242step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31242step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31242step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31243 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31243step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31243step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31243step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31243step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31244 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31244step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31244step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31244step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31244step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31244step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31245 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31245Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31245step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31245step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31246 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31246Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31246step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31247 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31247Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31247step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw31247step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31247step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31247step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31248step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31248step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31248step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31248step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31249 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31249step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31249step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31250 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31250step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31251 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31251step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw31251step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31251step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw31251step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31252step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31253 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31253step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31254 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31254step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31255step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31256 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31257 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31258 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31259 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31259Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31259step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw31259step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31259step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31259step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31260step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw31260step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31260step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31261 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31261step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw31261step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31261step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31262 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31262step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31263 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31263step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31264 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw31264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw31264step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw31264step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31264step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31264step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31270Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31270step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw31271Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw31271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw31272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw31272step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw31276step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31276step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31276step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31276step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw31277step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31277step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31277step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31277step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw31278step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31278step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31278step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw31279step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31279step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31279step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31279step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31279step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw31280step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31280step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31280step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31280step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31281step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31282step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31285step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw31296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw31297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw31298step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw31299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw31300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw31300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31303step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31303step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31303step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31303step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31304step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31304step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31304step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31304step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw31305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw31306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw31306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31307step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31307step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw31308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31309Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31309step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw31309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31310Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31310step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw31310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31311Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31311step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31311step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31311step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31311step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31312Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31312step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31312step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31312step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw31312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31313Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31313step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31314Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31314step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31314step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31314step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31314step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw31314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31314step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw31314step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31315Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31315step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31315step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31315step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw31315step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31316Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31316step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31317Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31317step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31318Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31319Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31319step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw31319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31320Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31320step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw31320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31321Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31322Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31323Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31324Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31325Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31326Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31326step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw31326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31327Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31327step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw31327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31328Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31328step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31328step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31329Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31329step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw31330Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw31330step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31331Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31331step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw31331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31332Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31332step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw31332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31332step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31333Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31333step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31333step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31334step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw31335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31335step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31336Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31336step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw31336step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31336step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31336step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31336step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31337Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31337step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw31337step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31337step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31337step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31337step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31337step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31338Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw31338step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31338step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31338step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31339Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31339step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw31339step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31339step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31339step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31339step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31340Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31340step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw31340step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31340step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31340step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31340step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31341Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31341step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31341step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31341step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31341step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw31341step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31341step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31341step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31341step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31341step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31342Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31342step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31342step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31342step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31342step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw31342step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31342step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31342step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31342step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31342step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31343Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31343step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw31343step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31343step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31343step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31343step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31344Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31344step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31344step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31344step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw31344step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31344step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31344step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31344step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31344step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31345Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31345step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31345step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31345step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw31345step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31345step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31345step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31345step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31345step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31346Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31346step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw31346step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31346step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw31346step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31346step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw31346step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31347Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31347step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw31347step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31347step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw31347step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31347step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw31347step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31348Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw31348step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw31348step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31348step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw31348step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31349Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31349step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw31349step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw31349step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31349step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw31349step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31350Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31350step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31350step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31350step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31350step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31350step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31351Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw31351step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31351step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31351step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31351step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31352Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw31352step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31352step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31352step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31352step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31353Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw31353step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31353step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31353step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31353step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31353step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31354Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw31354step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31354step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31354step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31354step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31355Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw31355step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31355step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31355step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31355step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31355step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31356Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31356step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw31356step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31356step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw31356step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31356step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw31356step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31357Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31357step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw31357step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw31357step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31357step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw31357step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31358Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31358step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw31358step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw31358step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31358step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw31358step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31359Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw31359step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw31359step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31359step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw31359step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical245
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw31360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw31360Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw31360step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw31360step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31360step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw31360step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31360step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw31360step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31361Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31361step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw31361step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31361step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw31361step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31361step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw31361step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31362Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31362step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw31362step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw31362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31363Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31363step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw31363step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw31363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31364Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw31364step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31364step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw31364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw31365Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31365step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw31365step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw31365step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31365step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw31365step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw31370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31380step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31380step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31380step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw31381step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31381step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31381step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31381step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31381step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw31382step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31382step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31382step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31382step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw31383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31383step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31383step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31383step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw31384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31384step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31384step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31384step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31385step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31385step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31386step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31386step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31387step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw31388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31388step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31388step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31389step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31390step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31390step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31391step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31391step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31392step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31392step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -3, 0], ![2, 0, -2]]
def raw31393step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw31393step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31393step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw31393step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![3, -3, 0], ![2, 0, -2]]
def raw31394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw31394step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw31394step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![3, -3, 0], ![2, 0, -2]]
def raw31395step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw31395step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw31395step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31395step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw31395step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw31396step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw31396step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31396step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw31396step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw31397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -3, 0], ![1, 1, -2]]
def raw31397step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw31397step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw31397step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, -1, -2]]
def raw31398step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31398step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31398step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31398step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![3, -1, -2]]
def raw31399step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31399step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31399step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31399step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![3, -1, -2]]
def raw31400step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31400step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31400step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31401step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31401step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31426 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31426step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw31426step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw31426step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31429 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31429step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31434step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31434step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31434step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31434step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31434step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31457step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31457step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31457step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31457step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31457step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31457step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31458step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31458step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31458step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31458step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31458step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31458step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31459step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31459step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31459step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31459step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31460step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw31460step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31460step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31460step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31460step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31461step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw31461step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31461step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31461step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31461step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31462step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31462step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31462step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31463step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31464step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31464step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31465step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31466step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31466step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31466step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw31481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw31486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 2, -1], ![-1, 0, 1]]
def raw31487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw31487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical246
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw31488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw31488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw31488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![-1, 0, 1]]
def raw31489step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw31489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw31490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31490step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw31490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31491step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw31491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31491step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw31491step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31492step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31492step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31493step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31493step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31493step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw31493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31495step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31495step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31495step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw31495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31496step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31496step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31496step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw31496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31507step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw31507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31508step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw31508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw31511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31512step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw31512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31513step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw31513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31514step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw31516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31516step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31517step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31517step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31517step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31517step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31517step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31518step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31518step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31518step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31518step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31519step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31519step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31520step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw31520step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31520step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31520step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31520step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31521step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw31521step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31521step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31521step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31521step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31522step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31522step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31522step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31522step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31522step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31522step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31522step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31522step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31523step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31523step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31523step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31523step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31523step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31523step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31523step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31524step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31524step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31524step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31524step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31524step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31524step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31525Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31525step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31525step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw31525step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31525step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31525step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31525step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31525step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31526step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31526step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw31526step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31526step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31526step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31526step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31526step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31527Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31527step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31527step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31527step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw31527step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31527step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw31527step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31528step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw31528step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31528step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw31528step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31529Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31529step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw31529step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31529step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw31529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31530step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw31530step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw31530step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31530step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw31530step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31531Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31531step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw31531step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw31531step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31531step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw31531step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31532Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31532step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31532step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31532step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31532step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31533Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31533step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31533step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31533step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31533step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31534Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31534step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31534step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31534step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31535Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw31535step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31535step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31535step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31536Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw31536step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31536step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31536step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31537Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31537step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw31537step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31537step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31537step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31537step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31537step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31538Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31538step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw31538step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31538step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31538step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31538step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31538step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31539Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31539step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw31539step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31539step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31539step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31539step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31540Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw31540step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31540step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31540step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31541Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw31541step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw31541step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw31541step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31541step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw31541step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31542Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31542step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw31542step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31542step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31542step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31542step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31543Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31543step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw31543step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31543step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31543step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31543step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31544Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31544step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw31544step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31544step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31544step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31544step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31545Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw31545step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31545step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31545step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw31546Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31546step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw31546step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw31546step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31546step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw31546step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31553 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw31553Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31553step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]
def raw31553step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31553step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw31553step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31562step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31562step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31563step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31563step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31564step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31564step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw31565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw31565step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw31565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31566step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31566step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31567step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31567step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31568step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw31569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31569step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31570step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31571step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31572step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31572step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw31573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31573step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31573step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31573step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw31574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31574step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![3, -2, -1], ![2, -1, -1]]
def raw31575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31575step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31575step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31576step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31576step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31576step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -2, -1], ![1, 0, -1]]
def raw31577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31577step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31577step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw31578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31578step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31578step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw31579step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31579step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31579step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31579step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![3, -2, -1]]
def raw31580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31580step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31580step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31581step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw31604step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw31604step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31604step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw31604step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31605 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31605step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31606 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw31606step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw31606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31607step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31607step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31607step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31607step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31608step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31608step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31608step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31608step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31609 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31609step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31609step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

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

def raw31625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31625step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31625step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw31625step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31625step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw31625step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31626step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31626step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31627step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31627step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31628step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw31628step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31628step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw31628step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31629step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31629step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31629step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw31629step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31629step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw31629step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31630step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31630step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 1, -3], ![2, -2, 0]]
def raw31630step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31630step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw31630step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end


