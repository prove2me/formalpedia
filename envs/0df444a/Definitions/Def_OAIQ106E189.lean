-- Prove2me | Definitions.Def_OAIQ106E189
-- name    : OAIQ106E189
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:32:30.106514+00:00
-- url     : https://prove2.me/theorems/41e4ad72-1b1f-4971-b4f6-0fc20668e81e
-- title:
--   Definitions bundle OAIQ106E189 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2046 declarations of OpenAI's Lean: 2046 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw21792step0`, `OAI.MUB6.Certificate.MixedSemantics.raw21792step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21792step1`, `OAI.MUB6.Certificate.MixedSemantics.raw21792step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21793`, `OAI.MUB6.Certificate.MixedSemantics.raw21793Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21793step0`, `OAI.MUB6.Certificate.MixedSemantics.raw21793step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21793step1`, `OAI.MUB6.Certificate.MixedSemantics.raw21793step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21794`, `OAI.MUB6.Certificate.MixedSemantics.raw21794Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21794step0`, `OAI.MUB6.Certificate.MixedSemantics.raw21794step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21794step1`, `OAI.MUB6.Certificate.MixedSemantics.raw21794step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21795`, `OAI.MUB6.Certificate.MixedSemantics.raw21795Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21795step0`, `OAI.MUB6.Certificate.MixedSemantics.raw21795step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21795step1`, `OAI.MUB6.Certificate.MixedSemantics.raw21795step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21795step2`, `OAI.MUB6.Certificate.MixedSemantics.raw21795step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21796`, `OAI.MUB6.Certificate.MixedSemantics.raw21796Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21796step0`, `OAI.MUB6.Certificate.MixedSemantics.raw21796step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21796step1`, `OAI.MUB6.Certificate.MixedSemantics.raw21796step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21796step2`, `OAI.MUB6.Certificate.MixedSemantics.raw21796step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21797`, `OAI.MUB6.Certificate.MixedSemantics.raw21797Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21797step0`, `OAI.MUB6.Certificate.MixedSemantics.raw21797step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21797step1`, `OAI.MUB6.Certificate.MixedSemantics.raw21797step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw21798`, `OAI.MUB6.Certificate.MixedSemantics.raw21798Labels` and 2006 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical0.lean), [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical17`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical17.lean), [`MutuallyUnbiased_MixedSemantics_Canonical170`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical170.lean), [`MutuallyUnbiased_MixedSemantics_Canonical171`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical171.lean), [`MutuallyUnbiased_MixedSemantics_Canonical172`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical172.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1162_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1163_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2570_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5167_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5168_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5169_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound26_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound40_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound74_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound75_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound95_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound446_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound744_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound974_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990_e`.
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

def raw21Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw21step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw22 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]

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

def raw217Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw217step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw217step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw220 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]

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

def raw2179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw2179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2180 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw2180Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw2180step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw2180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw2180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2181 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2181step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2181step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2182 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2182Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2183 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2183Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw2183step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw2183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2183step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw2183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2184 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw2184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw2184step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw2184step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2185 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw2185Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw2185step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2186 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw2186Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-2, 2, 0]]
def raw2186step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]
def raw2186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]
def raw2186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2187 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2187step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2187step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2188 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2188Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2188step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2189 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2189Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2189step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2189step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2189step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2190 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2190step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2190step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2191 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2192 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2192Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw2192step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2193 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2193step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2194 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2195 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2195Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2195step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2195step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2195step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2196 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2196step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2196step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2197 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2197step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2198 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2198Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw2198step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw2198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw2198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2199 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2199step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2200 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2201 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2201Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2201step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2201step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2201step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2202 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2202step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2202step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2203 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2204 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2204Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw2204step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw2204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw2204step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2205 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 3, -2]]
def raw2205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2205step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw2205step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw2205step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2206 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 3, -2]]
def raw2206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2206step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw2206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2207 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 3, -2]]

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

def raw21792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21795step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw21795step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21796step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21796step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw21796step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21797step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21799step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21800step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21800step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21800step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21800step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21801step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21801step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21801step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21801step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21801step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21801step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21801step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21802step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21802step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21802step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21802step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21802step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21802step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21802step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21803step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21803step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21803step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21803step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21803step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21803step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21803step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21803step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21804step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21804step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21804step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21804step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21804step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-2, -1, 3]]
def raw21804step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21804step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw21804step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21804step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw21804step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21805step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21805step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21805step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![2, 0, -2]]
def raw21805step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21805step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw21805step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21806step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21806step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21806step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21806step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21806step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21806step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21806step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21806step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21807step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21807step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21807step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21807step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21807step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21807step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21808step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21808step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21808step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21808step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21809Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21809step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21809step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21809step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21809step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21809step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21809step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21809step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21810Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21810step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21810step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw21810step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21810step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21810step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21810step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21810step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21811Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21811step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21811step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21811step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21811step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21811step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21811step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21811step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21811step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21811step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21812Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21812step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21812step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21812step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21812step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21813Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21813step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21813step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21813step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21813step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21813step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21813step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21814step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21814step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21814step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21814step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21814step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21814step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21814step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21814step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21815step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21815step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21815step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21815step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw21815step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21815step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21815step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21815step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21815step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21816step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21816step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21816step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21816step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21816step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21816step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21816step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21816step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21816step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21817step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21817step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21817step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21817step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21817step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21818step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21818step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21818step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21818step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21818step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21819step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21819step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21819step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21819step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21819step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21819step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21819step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21819step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21819step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21820Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21820step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21820step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21820step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw21820step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21820step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21820step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21820step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21820step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21821Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21821step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21821step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21821step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw21821step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21821step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -1, 2], ![-2, -1, 3]]
def raw21821step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21821step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw21821step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21821step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw21821step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21822Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21822step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21822step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21822step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21822step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw21822step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21822step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21822step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21822step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21822step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21823Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21823step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21823step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21823step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw21823step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21823step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21823step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21823step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21823step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21824Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21824step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21824step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21824step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw21824step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21824step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21824step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21824step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21824step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21825Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21825step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21825step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21825step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw21825step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21825step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw21825step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21825step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw21825step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21825step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw21825step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21826Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21826step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21826step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21826step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21826step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw21826step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21826step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-2, -2, 4]]
def raw21826step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21826step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw21826step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21826step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw21826step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21827Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21827step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21827step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21827step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw21827step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21827step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21827step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21827step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21827step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21828Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21828step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21828step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21828step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21828step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw21828step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21828step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21828step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21828step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21828step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21829Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21829step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21829step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21829step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw21829step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21829step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21829step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21829step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21829step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21830Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21830step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21830step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21830step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21830step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21830step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw21830step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21830step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw21830step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21830step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw21830step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21832step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21832step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21833step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21833step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21834step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw21834step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21834step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw21834step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21834step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21834step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21834step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21834step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21835step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21836step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21837step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21838step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21838step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21839step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21839step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21840step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21841step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21842step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21843step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21846step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21847step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw21847step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21848step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21849step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21849step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21849step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21850step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21850step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21850step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21851step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw21851step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21852step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21852step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21852step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![4, -1, -3]]
def raw21852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21852step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw21852step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21853Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21853step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21853step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21853step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21853step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21853step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21854Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21854step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21854step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21854step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21854step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21854step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21854step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21854step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21855Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21855step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21855step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21855step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21855step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21855step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21855step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21855step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21856Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21856step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21856step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21856step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21856step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw21856step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21856step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw21856step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21856step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21856step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21856step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21856step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21857Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21857step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21857step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21857step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21857step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21857step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21857step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21857step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21857step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21858Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21858step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21858step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21858step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21858step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21859Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21859step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21859step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21859step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21859step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21859step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21860Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21860step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21860step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21860step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw21860step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21860step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21860step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21860step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21860step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21861Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21861step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21861step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21861step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21861step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21861step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21861step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21861step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21862Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21862step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21862step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21862step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21862step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21862step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21863Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21863step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21863step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21863step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21863step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21863step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21864Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21864step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21864step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21864step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw21864step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21864step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21864step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21864step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21864step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21865Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21865step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21865step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21865step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21865step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21865step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21865step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21865step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21865step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21866Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21866step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21866step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21866step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21866step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21866step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21867Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21867step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21867step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21867step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21867step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21867step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21868Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21868step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21868step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw21868step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21868step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21868step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21868step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21868step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21869Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21869step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21869step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21869step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw21869step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21869step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-3, 0, 3]]
def raw21869step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21869step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw21869step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21869step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw21869step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21870Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21870step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21870step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw21870step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21870step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21870step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21870step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21870step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21871Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21871step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21871step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21871step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw21871step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21871step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21871step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21871step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21871step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21872Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21872step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21872step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21872step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw21872step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21872step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21872step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21872step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21872step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21873Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21873step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21873step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21873step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw21873step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21873step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw21873step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21873step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw21873step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21873step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw21873step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21874Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21874step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21874step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21874step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![4, -1, -3]]
def raw21874step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21874step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw21874step3Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21874step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -1, 4], ![3, 1, -4]]
def raw21874step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21874step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -1, 4], ![3, 1, -4]]
def raw21874step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21875step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw21875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21876step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21879step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw21879step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw21882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw21882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw21882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21882step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw21882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21887step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical171
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw21888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw21888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw21888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw21888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21890 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![-1, 1], ![3, -3], ![1, -1]]
def raw21890Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21890step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![3, -3], ![1, -1]]
def raw21890step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21890step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![3, -3], ![1, -1]]
def raw21890step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21890step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw21890step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw21891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw21892step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21893step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw21894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw21894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw21894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21898step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21901 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw21901Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21901step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw21901step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21901step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw21901step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw21906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw21906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw21906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw21909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw21909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw21909step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw21910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw21911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21918step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21918step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21918step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21919step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21919step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21920step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21920step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21920step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw21920step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw21920step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw21920step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21921step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21921step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21921step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21921step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21922step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21922step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21922step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw21922step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21922step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21922step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21922step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21922step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21923step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21925step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21926step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw21927step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21928step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21930step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21931step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw21932step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw21936step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21937step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21938step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw21944step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21944step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw21945step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21945step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21946step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21948step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21949step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21950step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21950step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21950step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw21950step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21951step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21951step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21951step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21951step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21951step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21952step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21952step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw21952step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21952step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21952step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21952step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21952step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21953step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21953step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21953step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21953step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21954step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21954step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21954step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21955step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21955step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21955step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21955step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21956step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21956step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21956step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21956step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21957step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21957step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21957step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21957step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21957step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21957step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21958step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21958step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21958step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21958step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21959step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21959step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21959step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21960step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21960step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21960step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21960step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21960step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21961step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21961step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21961step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21961step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21962step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21962step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21962step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21962step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21963Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21963step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21963step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21963step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21963step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21963step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21963step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21963step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21964Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21964step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21964step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21964step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21964step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21964step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21965Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21965step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21965step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21965step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21965step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21965step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21966Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21966step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21966step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21966step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21966step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21966step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21966step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21966step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21967Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21967step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21967step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21967step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21967step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21967step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21967step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21967step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21967step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21968Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21968step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21968step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21968step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw21968step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21968step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw21968step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21968step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw21968step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21969Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21969step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 0, 3]]
def raw21969step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21969step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21969step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21969step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21970Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21970step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 0, 3]]
def raw21970step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21970step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21970step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21970step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21971Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21971step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21971step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, -1, 2], ![-3, 0, 3]]
def raw21971step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21971step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21971step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21971step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21971step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21972Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21972step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21972step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw21972step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21972step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21972step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21972step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21973Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21973step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21973step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21973step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-3, -1, 4]]
def raw21973step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21973step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![3, 1, -4]]
def raw21973step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21973step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![3, 1, -4]]
def raw21973step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21974Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21974step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw21974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw21974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21975Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21975step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw21975step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw21975step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21976Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21976step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21976step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![3, 1, -4]]
def raw21976step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![3, 1, -4]]
def raw21976step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21977step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21977step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw21977step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21977step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw21977step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21980Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21980step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw21983step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21984 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![-1, 1], ![1, -1], ![3, -3]]
def raw21984Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21984step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![1, -1], ![3, -3]]
def raw21984step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21984step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw21984step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21991 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21991step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21991step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![0, -1, 1], ![0, -3, 3]]
def raw21991step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21991step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw21991step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw21991step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw21991step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw21991step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw21991step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21994 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw21994step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21994step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw21994step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21994step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw21994step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw22002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw22006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw22006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw22007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw22007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw22007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22008 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![0, 0], ![1, -1], ![0, 0]]
def raw22008Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22008step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![0, 0], ![1, -1]]
def raw22008step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22008step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]
def raw22008step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22008step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22008step2Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical172
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22016step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, 0, -2], ![2, -2, 0]]
def raw22020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22020step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22020step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw22021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22022 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![0, 0], ![2, -2], ![0, 0]]
def raw22022Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22022step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![0, 0], ![2, -2]]
def raw22022step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22022step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![2, -2]]
def raw22022step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22022step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw22022step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22023step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw22023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22024step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![3, -2, -1]]
def raw22024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw22025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw22026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw22027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw22027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![3, -2, -1]]
def raw22027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw22027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw22028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22029 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]
def raw22029Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22029step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![1, -1], ![1, -1]]
def raw22029step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22029step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]
def raw22029step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22029step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22029step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw22034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw22034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw22037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22040 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw22040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw22040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22040step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw22040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22040step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw22040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22040step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22040step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22041step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22044step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![3, -1, -2]]
def raw22045step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22045step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw22045step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22047 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]
def raw22047Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22047step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![0, 0], ![2, -2]]
def raw22047step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22047step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![2, -2]]
def raw22047step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22047step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw22047step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22048step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22048step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22048step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22049step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22050step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22051step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22051step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![3, -1, -2]]
def raw22051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22051step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]
def raw22051step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22052step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22052step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22056step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw22056step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22056step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22056step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22057 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw22057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22057step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22064 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]
def raw22064Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22064step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw22064step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw22065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw22066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw22067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw22068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw22070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22071 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]
def raw22071Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22071step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw22071step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22078Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


